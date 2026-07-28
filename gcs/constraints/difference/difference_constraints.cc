#include <gcs/constraints/difference/difference_constraints.hh>
#include <gcs/constraints/difference/difference_graph.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/reification.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <map>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::map;
using std::move;
using std::optional;
using std::shared_ptr;
using std::size_t;
using std::string;
using std::to_string;
using std::unique_ptr;
using std::vector;

namespace
{
    // Reduce an operand to (bare variable, offset), so that V = *variable +
    // offset. A constant operand has no variable, just the offset.
    //
    // A negated view is rejected outright: V - W <= d with V = -X + c is
    // -X - W <= d - c, which is not a difference constraint (both coefficients
    // are negative). Getting this wrong is unsound rather than merely
    // incomplete, so it is a hard error at construction. See the survey's
    // section 2.6(e). The shared helper reports it by returning nullopt,
    // because a presolver has to skip such a constraint rather than reject the
    // model it appears in.
    auto deview_operand(const IntegerVariableID & var, const char * which) -> DeviewedDifferenceOperand
    {
        auto result = deview_difference_operand(var);
        if (! result)
            throw InvalidProblemDefinitionException{
                string{"DifferenceConstraints "} + which + " operand is a negated view, which is not a difference constraint"};
        return *result;
    }
}

DifferenceConstraints::DifferenceConstraints(vector<DifferenceEdge> edges) : _edges(move(edges))
{
    // Reject negated views up front, so a bad model is a post-time error rather
    // than a mysterious proof failure much later. prepare() redoes the
    // deviewing; this is a cheap guard, not the canonicalisation itself.
    for (const auto & e : _edges) {
        static_cast<void>(deview_operand(e.x, "left"));
        static_cast<void>(deview_operand(e.y, "right"));
    }
}

auto DifferenceConstraints::simplifying_at_root(bool simplify) -> DifferenceConstraints &
{
    _simplify.enabled = simplify;
    return *this;
}

auto DifferenceConstraints::reporting_simplification_to(shared_ptr<DifferenceSimplificationStats> stats) -> DifferenceConstraints &
{
    _simplify.stats = move(stats);
    return *this;
}

auto DifferenceConstraints::clone() const -> unique_ptr<Constraint>
{
    auto result = make_unique<DifferenceConstraints>(_edges);
    result->simplifying_at_root(_simplify.enabled);
    result->reporting_simplification_to(_simplify.stats);
    return result;
}

auto DifferenceConstraints::prepare(Propagators &, State &, ProofModel * const) -> bool
{
    if (_edges.empty())
        return false;

    map<SimpleIntegerVariableID, size_t> node_of;
    auto node_index = [&](const SimpleIntegerVariableID & v) -> size_t {
        auto [it, inserted] = node_of.emplace(v, _graph.nodes.size());
        if (inserted)
            _graph.nodes.push_back(v);
        return it->second;
    };

    for (size_t i = 0; i < _edges.size(); ++i) {
        const auto & e = _edges[i];
        auto left = deview_operand(e.x, "left");
        auto right = deview_operand(e.y, "right");

        // (X + c1) - (Y + c2) <= d  becomes  X - Y <= d - c1 + c2, so every
        // edge's weight is expressed over bare variables and nothing else.
        auto d = e.d - left.offset + right.offset;

        // A degenerate edge says 0 <= d. Unconditionally that is vacuous when
        // d >= 0 and a root contradiction when d < 0. Half-reified it is
        // vacuous when d >= 0 and says `!cond' when d < 0 --- which has to be
        // *said*, since dropping it would let cond hold with the constraint
        // violated. The propagator does that from the same row, so no
        // initialiser is involved and a presolver could do the same.
        auto degenerate = [&](Integer weight) {
            if (weight >= 0_i)
                return;
            if (e.cond)
                _graph.disallowed_conditions.push_back(DifferenceDisallowedCondition{*e.cond, i});
            else if (! _root_contradiction_posted_index)
                _root_contradiction_posted_index = i;
        };

        if (left.variable && right.variable) {
            auto from = node_index(*left.variable);
            auto to = node_index(*right.variable);
            if (from == to)
                degenerate(d);
            else
                _graph.edges.push_back(DifferenceGraphEdge{from, to, d, i, e.cond});
        }
        else if (left.variable) {
            // X - c2 <= d, i.e. X <= d (c2 already folded in above).
            _graph.static_bounds.push_back(DifferenceStaticBound{node_index(*left.variable), d, false, i, e.cond});
        }
        else if (right.variable) {
            // c1 - Y <= d, i.e. Y >= -d.
            _graph.static_bounds.push_back(DifferenceStaticBound{node_index(*right.variable), -d, true, i, e.cond});
        }
        else {
            // Two constants: 0 <= d, exactly as for aliasing.
            degenerate(d);
        }
    }

    return true;
}

auto DifferenceConstraints::define_proof_model(ProofModel & model, const State &) -> void
{
    // One labelled row per posted edge, role e<i> with i the edge's position in
    // the posted list, so a proof line can be traced back to the edge the user
    // wrote. Nothing else goes in: no flags, no auxiliaries. Every inference
    // this constraint makes is a cutting-planes consequence of these rows.
    //
    // The row is emitted over the *canonical* (deviewed) operands, with the
    // views' offsets folded into the right hand side, rather than over the
    // user's operands. This is deliberate, and it is what makes the proofs
    // work: the negative-cycle refutation and the bound pushes both rely on
    // consecutive edges' shared variable cancelling exactly, and
    // dev_docs/view-proof-logging.md invariant 1 says that only happens when
    // both rows express it in the same representation. A registered view V of X
    // has its own bit-vector, related to BinEnc(X) only by the link axiom, so
    // two edges meeting at "the same variable" through different views would
    // not cancel at all. Emitting the deviewed form removes the problem by
    // construction, and it is still definitional: X - Y <= d - c1 + c2 states
    // exactly the posted V1 - V2 <= d, just written in the bare variables'
    // bits. (The alternative would be to emit in the user's operands and use
    // PolBuilder::enable_deview_mode, as linear/justify.cc does; that is
    // strictly more machinery for the same result here, since this constraint
    // owns both ends of every cancellation.)
    _graph.edge_lines.reserve(_edges.size());
    for (size_t i = 0; i < _edges.size(); ++i) {
        const auto & e = _edges[i];
        auto left = deview_operand(e.x, "left");
        auto right = deview_operand(e.y, "right");
        auto d = e.d - left.offset + right.offset;

        WPBSum sum;
        if (left.variable)
            sum += 1_i * IntegerVariableID{*left.variable};
        if (right.variable)
            sum += -1_i * IntegerVariableID{*right.variable};

        // An aliased edge leaves the same variable in the sum twice with
        // opposite coefficients, and a two-constant edge leaves the sum empty:
        // both render as a row whose left hand side is zero, which is exactly
        // what 0 <= d says, and which VeriPB reads as trivially true or
        // directly false according to d's sign.
        //
        // A half-reified edge's row is emitted under HalfReifyOnConjunctionOf,
        // so it says `cond -> X - Y <= d' and carries a big-M term on `~cond'.
        // That term does not telescope, which is the point: it survives every
        // sum as a residual and saturates into exactly the clause the propagator
        // is entitled to learn. An unconditional edge passes nullopt and its row
        // is byte-for-byte what it was before conditions existed.
        optional<HalfReifyOnConjunctionOf> half_reif;
        if (e.cond)
            half_reif = HalfReifyOnConjunctionOf{*e.cond};

        _graph.edge_lines.push_back(model.add_labelled_constraint(constraint_id(), "e" + to_string(i), move(sum) <= d, half_reif));
    }
}

auto DifferenceConstraints::install_propagators(Propagators & propagators) -> void
{
    if (_root_contradiction_posted_index) {
        // The edge's own OPB row is `0 >= something positive', so the
        // contradiction is RUP from the model with no state involved at all.
        // Deliberately not part of install_difference_propagator: this is an
        // initialiser, and initialisers have already run by the time a
        // presolver builds a graph, so the presolver must instead decline to
        // lift a degenerate edge and leave it to its own propagator.
        propagators.install_initial_contradiction("difference constraint x - x <= d with d < 0", JustifyUsingRUP{}, NoReason{});
        return;
    }

    install_difference_propagator(propagators, constraint_id(), move(_graph), move(_simplify));
}

auto DifferenceConstraints::constraint_type() const -> string
{
    return "difference";
}

auto DifferenceConstraints::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();

    vector<SExpr> edges;
    for (const auto & e : _edges) {
        vector<SExpr> edge{tracker.s_expr_term_of(e.x), tracker.s_expr_term_of(e.y), SExpr::atom(e.d.to_string())};
        // A half-reified edge carries its condition as a fourth element, so
        // that an unconditional system's s-expression is unchanged.
        if (e.cond)
            edge.push_back(tracker.s_expr_term_of(Literal{*e.cond}));
        edges.push_back(SExpr::list(move(edge)));
    }

    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(move(edges))});
}
