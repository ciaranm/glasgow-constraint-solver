#include <gcs/constraints/comparison/comparison.hh>
#include <gcs/constraints/difference/difference_graph.hh>
#include <gcs/constraints/linear/linear_greater_than_equal.hh>
#include <gcs/constraints/linear/linear_inequality.hh>
#include <gcs/constraints/linear/linear_less_than_equal.hh>
#include <gcs/exception.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/presolvers/difference_logic.hh>
#include <gcs/problem.hh>
#include <gcs/reification.hh>

#include <util/overloaded.hh>

#include <concepts>
#include <map>
#include <memory>
#include <optional>
#include <span>
#include <string>
#include <utility>
#include <variant>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::map;
using std::move;
using std::nullopt;
using std::optional;
using std::shared_ptr;
using std::size_t;
using std::string;
using std::to_string;
using std::unique_ptr;
using std::vector;

namespace
{
    // The type strings the two donor families report. Constraint::constraint_type()
    // is total and independent of the C++ class hierarchy, which is exactly what
    // makes it usable as a cross-check on the hierarchy: see check_enumeration_is_working.
    const string linear_inequality_type = "lin_less_equal";

    auto is_comparison_type(const string & t) -> bool
    {
        return t == "less_than" || t == "less_equal" || t == "greater_than" || t == "greater_equal";
    }

    // The failure this exists to catch is a silent one, so it says so at length.
    // Problem stores what Constraint::clone() returns, and every member of these
    // families currently clones to its family base, which is why asking for the
    // base is what finds a posted LinearLessThanEqual. If that ever stops being
    // true, each_constraint_of_type<ReifiedLinearInequality>() yields nothing, the
    // presolver lifts nothing, and *every* validation still passes: a presolver
    // that does nothing preserves the solution set, adds no OPB content and leaves
    // every proof verifying. So cross-check the typed enumeration against
    // constraint_type(), which does not depend on the hierarchy at all, and fail
    // loudly rather than quietly doing nothing.
    auto check_enumeration_is_working(const Problem & problem, size_t linears_seen, size_t comparisons_seen) -> void
    {
        size_t linears_by_type = 0, comparisons_by_type = 0;
        for (const auto & c : problem.each_constraint()) {
            auto type = c.constraint_type();
            if (type == linear_inequality_type)
                ++linears_by_type;
            else if (is_comparison_type(type))
                ++comparisons_by_type;
        }

        auto complain = [&](const string & family, const string & base, size_t by_type, size_t seen) {
            throw UnexpectedException{"the difference-logic presolver's constraint enumeration is broken: " + to_string(by_type) +
                " posted constraints report a " + family + " constraint_type(), but Problem::each_constraint_of_type<" + base + ">() yielded only " +
                to_string(seen) +
                " of them. DETECTION is what needs fixing here, not this check. The likely cause is a change to Constraint::clone() or to the class "
                "hierarchy, so that a posted constraint is no longer stored as its family base (see PR #585). Do NOT relax this check: a presolver "
                "that lifts nothing still passes every solution-equivalence, OPB byte-diff and VeriPB check, so this is the only thing standing "
                "between a silent regression and shipping. Fix gcs/presolvers/difference_logic.cc."};
        };

        if (linears_by_type > linears_seen)
            complain(linear_inequality_type, "ReifiedLinearInequality", linears_by_type, linears_seen);
        if (comparisons_by_type > comparisons_seen)
            complain(
                "less_than / less_equal / greater_than / greater_equal", "ReifiedCompareLessThanOrMaybeEqual", comparisons_by_type, comparisons_seen);
    }

    // One OPB row of the only shape this presolver can lift: `1 * positive +
    // -1 * negative <= value`, emitted under the bare @c[<id>] label and, when
    // `cond` is engaged, under HalfReifyOnConjunctionOf on that condition.
    //
    // Both donor families reduce to this, which is why the deview, degeneracy
    // and weight arithmetic below is written once. Note that the row, not the
    // constraint, is what is described: for a comparison stated negatively the
    // row's operands are the other way round from the ones the user posted.
    struct DifferenceRow
    {
        IntegerVariableID positive;
        IntegerVariableID negative;
        Integer value;
        optional<IntegerVariableCondition> cond;
    };
}

DifferenceLogic::DifferenceLogic(shared_ptr<DifferenceLogicStats> stats) :
    _stats(move(stats)), _disable_lifted_donors(false), _simplify(true), _incremental()
{
}

auto DifferenceLogic::disabling_lifted_donors(bool disable) -> DifferenceLogic &
{
    _disable_lifted_donors = disable;
    return *this;
}

auto DifferenceLogic::simplifying_at_root(bool simplify) -> DifferenceLogic &
{
    _simplify = simplify;
    return *this;
}

auto DifferenceLogic::reporting_simplification_to(shared_ptr<DifferenceSimplificationStats> stats) -> DifferenceLogic &
{
    _simplification_stats = move(stats);
    return *this;
}

auto DifferenceLogic::incrementally(bool incremental) -> DifferenceLogic &
{
    _incremental.enabled = incremental;
    return *this;
}

auto DifferenceLogic::auditing_incremental_propagation(bool audit) -> DifferenceLogic &
{
    _incremental.audit = audit;
    return *this;
}

auto DifferenceLogic::clone() const -> unique_ptr<Presolver>
{
    auto result = make_unique<DifferenceLogic>(_stats);
    result->disabling_lifted_donors(_disable_lifted_donors);
    result->simplifying_at_root(_simplify);
    result->reporting_simplification_to(_simplification_stats);
    result->incrementally(_incremental.enabled);
    result->auditing_incremental_propagation(_incremental.audit);
    return result;
}

auto DifferenceLogic::run(Problem & problem, Propagators & propagators, State & initial_state, ProofLogger * const logger) -> bool
{
    // Compile-time pins on the contract the enumeration below relies upon. The
    // helper matches the type Problem *stores*, which is what clone() returns,
    // and for both of these families that is the base; asking for the derived
    // user-facing type is not a compile error, it simply matches nothing. If a
    // future refactor breaks these relationships, this is the place that needs
    // to change, so fail here rather than at runtime. (The base being a base is
    // necessary but not sufficient --- clone() must also still return it --- so
    // check_enumeration_is_working covers the rest.)
    static_assert(std::derived_from<LinearLessThanEqual, ReifiedLinearInequality>);
    static_assert(std::derived_from<LinearLessThanEqualIf, ReifiedLinearInequality>);
    static_assert(std::derived_from<LinearGreaterThanEqual, ReifiedLinearInequality>);
    static_assert(std::derived_from<LessThan, ReifiedCompareLessThanOrMaybeEqual>);
    static_assert(std::derived_from<LessThanEqual, ReifiedCompareLessThanOrMaybeEqual>);
    static_assert(std::derived_from<LessThanEqualIf, ReifiedCompareLessThanOrMaybeEqual>);
    static_assert(std::derived_from<GreaterThan, ReifiedCompareLessThanOrMaybeEqual>);
    static_assert(std::derived_from<GreaterThanEqual, ReifiedCompareLessThanOrMaybeEqual>);
    static_assert(std::derived_from<GreaterThanEqualIf, ReifiedCompareLessThanOrMaybeEqual>);

    DifferenceLogicStats stats;

    DifferenceGraph graph;
    map<SimpleIntegerVariableID, size_t> node_of;
    auto node_index = [&](const SimpleIntegerVariableID & v) -> size_t {
        auto [it, inserted] = node_of.emplace(v, graph.nodes.size());
        if (inserted)
            graph.nodes.push_back(v);
        return it->second;
    };

    // The donors whose edges were lifted, for the optional disable below. Kept
    // as ids rather than pointers because that is what Propagators indexes by.
    // Half-reified donors are deliberately never added: see below.
    vector<ConstraintID> lifted_donors;

    // Turn one donor row into a graph edge, or account for why it cannot be.
    // Returns whether an edge was added, so a caller can also count the row in
    // whatever family bucket it belongs to. The graph does not care which
    // constraint class emitted the row --- only that the row exists, carries a
    // citable @c[<id>] label, and says `positive - negative <= value`.
    auto lift_row = [&](const DifferenceRow & row, const ConstraintID & id) -> bool {
        auto left = deview_difference_operand(row.positive);
        auto right = deview_difference_operand(row.negative);
        if (! left || ! right) {
            // A negated view: `-X - Y <= d` has both coefficients negative and
            // is not a difference constraint at all. Unsound to lift, not
            // merely unhelpful.
            ++stats.skipped_negated_view;
            return false;
        }

        // A constant operand makes this a plain bound, which the donor's own
        // propagator applies once and which adds nothing to the graph; and
        // aliasing says 0 <= d, which is vacuous, or else a root contradiction
        // (unconditionally, needing an initialiser --- and initialisers have
        // already run by the time a presolver is called) or a fact about the
        // condition (half-reified). Leave all of them to the donor, which
        // handles them. Checked before node_index is called, so a skipped edge
        // never leaves an isolated node behind to be triggered on.
        if (! left->variable || ! right->variable || *left->variable == *right->variable) {
            ++stats.skipped_degenerate;
            return false;
        }

        // (X + c1) - (Y + c2) <= d becomes X - Y <= d - c1 + c2, matching
        // DifferenceConstraints exactly. The donor's OPB row is still in the
        // user's views' bits; the propagator cites it in deview mode, which is
        // what puts it in the same representation as this arithmetic.
        auto d = row.value - left->offset + right->offset;
        auto from = node_index(*left->variable);
        auto to = node_index(*right->variable);

        auto posted_index = graph.edges.size();
        graph.edges.push_back(DifferenceGraphEdge{from, to, d, posted_index, row.cond});
        if (logger) {
            // The donor's own row, which both families label @c[<id>] with an
            // empty role, for the conditional forms exactly as for the
            // unconditional ones. Nothing new goes into the OPB ---
            // Presolver::run has no ProofModel * precisely because that door
            // has closed --- and nothing needs to: every inference the
            // propagator makes is a cutting-planes consequence of these rows.
            graph.edge_lines.push_back(ProofLineLabel{"c[" + as_string(id) + "]"});
        }

        if (row.cond)
            ++stats.half_reified_edges_lifted;
        else {
            // Only unconditional donors are candidates for retirement. A
            // half-reified donor also infers `!cond' from its own bounds, and
            // the global propagator infers nothing about a condition at all, so
            // retiring one would silently lose propagation.
            lifted_donors.push_back(id);
        }

        return true;
    };

    size_t linears_seen = 0;
    for (const auto & c : problem.each_constraint_of_type<ReifiedLinearInequality>()) {
        ++linears_seen;

        // MustHold gives a plain edge; If gives a half-reified one,
        // `cond -> x - y <= d'. Both are citable and both are the shape the
        // propagator's proofs assume: linear_inequality.cc labels the
        // unconditional row and the `If' row identically, @c[<id>] with an empty
        // role, and emits the latter under HalfReifyOnConjunctionOf on exactly
        // the condition recorded here.
        //
        // The other three kinds are each expressible as difference edges too.
        // Iff needs a *different* row of the donor's output: its two halves go
        // out under the roles r and f rather than under the empty role.
        // MustNotHold and NotIf state the integer negation, `y - x <= -d-1',
        // which is still a difference row --- MustNotHold's even under the
        // same empty role, NotIf's under `ltn' --- so those two are a
        // deliberate gap rather than an impossibility, and one to close for
        // the comparison family at the same time. Counted rather than guessed
        // at.
        auto liftable_kind = true;
        optional<IntegerVariableCondition> edge_condition;
        overloaded{
            [&](const reif::MustHold &) {},                             //
            [&](const reif::If & cond) { edge_condition = cond.cond; }, //
            [&](const auto &) { liftable_kind = false; }                //
        }
            .visit(c.reification_condition());

        if (! liftable_kind) {
            ++stats.skipped_reified;
            continue;
        }

        const auto & terms = c.coefficients_and_variables().terms;
        if (2 != terms.size()) {
            ++stats.skipped_not_two_terms;
            continue;
        }

        optional<IntegerVariableID> positive, negative;
        for (const auto & t : terms) {
            if (1_i == t.coefficient && ! positive)
                positive = t.variable;
            else if (-1_i == t.coefficient && ! negative)
                negative = t.variable;
        }
        if (! positive || ! negative) {
            ++stats.skipped_coefficients;
            continue;
        }

        static_cast<void>(lift_row(DifferenceRow{*positive, *negative, c.value(), edge_condition}, c.constraint_id()));
    }

    // Comparisons are difference constraints too --- `x <= y + d` is a view, not
    // a separate constraint kind --- and every row
    // ReifiedCompareLessThanOrMaybeEqual emits now carries an @label, so every
    // row is citable.
    size_t comparisons_seen = 0;
    for (const auto & c : problem.each_constraint_of_type<ReifiedCompareLessThanOrMaybeEqual>()) {
        ++comparisons_seen;

        // `x <= y` states `x - y <= 0` and `x < y` states `x - y <= -1`, both
        // under the bare @c[<id>] label; the `If' form states the same row
        // under HalfReifyOnConjunctionOf on the recorded condition, and under
        // the same label. Verified against cake_pb_cp, which is the other end
        // of that label: `less_equal', `less_than', `greater_equal',
        // `greater_than' and their `_if' spellings all come back as @c[<id>].
        //
        // The remaining three kinds are skipped, exactly as for the linear
        // family and for the same reasons, one of which no longer applies and
        // one of which still does. Iff's two halves are labelled @c[<id>][r]
        // and @c[<id>][f], neither of which is the row cited here. MustNotHold
        // and NotIf *are* now citable --- they state the integer negation,
        // `y - x <= -1' or `y - x <= 0', and they too go out under the bare
        // @c[<id>] --- but nothing in gcs constructs a
        // comparison with either (there is no user-facing class for them, and
        // s_expr() throws on both, so they have no .scp spelling either), and
        // the linear family leaves its own equally-citable MustNotHold row on
        // the floor as well. Lifting the negated forms is therefore a single
        // follow-up that should be done for both families at once, not an
        // asymmetry introduced here. Counted rather than guessed at.
        optional<DifferenceRow> row;
        overloaded{//
            [&](const reif::MustHold &) { row = DifferenceRow{c.left_variable(), c.right_variable(), c.or_equal() ? 0_i : -1_i, nullopt}; },
            [&](const reif::If & cond) { row = DifferenceRow{c.left_variable(), c.right_variable(), c.or_equal() ? 0_i : -1_i, cond.cond}; },
            [&](const auto &) {}}
            .visit(c.reification_condition());

        if (! row) {
            ++stats.skipped_reified;
            continue;
        }

        if (lift_row(*row, c.constraint_id()))
            ++stats.comparison_edges_lifted;
    }

    check_enumeration_is_working(problem, linears_seen, comparisons_seen);

    stats.edges_lifted = graph.edges.size();
    stats.nodes = graph.nodes.size();

    // Fewer than two edges is not a threshold, it is a degeneracy: over a single
    // edge the global propagator computes exactly what that edge's own
    // propagator computes, so installing it buys nothing and costs a wake. No
    // further gating is applied --- see dev_docs/difference-logic.md for why a
    // real threshold is not shipped.
    if (graph.edges.size() >= 2) {
        // A presolver-derived propagator has no posted-constraint identity of
        // its own, exactly as for AutoTable.
        install_difference_propagator(propagators, initial_state, CurrentlyUnnamedConstraint{}, move(graph),
            DifferenceSimplificationOptions{_simplify, _simplification_stats}, _incremental);
        stats.propagator_installed = true;

        if (_disable_lifted_donors)
            stats.donor_propagators_disabled = propagators.disable_propagators_for_constraints(lifted_donors);
    }

    if (_stats)
        *_stats = stats;

    return true;
}
