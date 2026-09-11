#include <gcs/constraints/in/hints.hh>
#include <gcs/constraints/in/in.hh>
#include <gcs/constraints/innards/justify_not_in_range.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/large_domain_guard.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>

#include <algorithm>
#include <optional>
#include <sstream>
#include <string>
#include <utility>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using namespace gcs;
using namespace gcs::innards;

using std::erase_if;
using std::make_unique;
using std::move;
using std::optional;
using std::string;
using std::unique_ptr;
using std::vector;
using std::ranges::any_of;
using std::ranges::binary_search;
using std::ranges::sort;
using std::ranges::unique;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
using std::print;
#else
using fmt::format;
using fmt::print;
#endif

In::In(IntegerVariableID var, vector<IntegerVariableID> vars, vector<Integer> vals) : _var(var), _var_vals(move(vars)), _val_vals(move(vals))
{
}

In::In(IntegerVariableID var, vector<IntegerVariableID> vals) : _var(var), _var_vals(move(vals))
{
}

In::In(IntegerVariableID var, vector<Integer> vals) : _var(var), _val_vals(move(vals))
{
}

auto In::clone() const -> unique_ptr<Constraint>
{
    return make_unique<In>(_var, _var_vals, _val_vals);
}

auto In::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    // Move members that are *syntactically* constant into the value list, but
    // leave a variable alone even when its domain has collapsed to one value.
    //
    // The distinction is what keeps the flag indices agreeing with cake_pb_cp's.
    // s_expr() runs on the stored constraint, before this, so the `.scp` lists
    // the members as posted: a ConstantIntegerVariableID renders as its integer,
    // which cake also reads as a constant, but a singleton-domain variable
    // renders as its name, and cake gives it a per-position flag triple like any
    // other variable. Folding it here would shift every later member's index and
    // leave the two encodings naming different things -- for In{A, {W, C}} with
    // W in [3,3], cake builds x[id][0][..] for W and x[id][1][..] for C while we
    // would build one triple, for C, called index 0.
    //
    // The fixed member's own flag triple is then dead weight in the OPB, which is
    // fine: cake carries exactly the same rows, and propagation is unaffected
    // (the propagator reads domains, not this partition).
    erase_if(_var_vals, [&](const IntegerVariableID & v) -> bool {
        if (! is_constant_variable(v))
            return false;
        _val_vals.push_back(*initial_state.optional_single_value(v));
        return true;
    });

    sort(_val_vals);
    _val_vals.erase(unique(_val_vals).begin(), _val_vals.end());

    if (_var_vals.empty() && _val_vals.empty()) {
        // No sources means the constraint is UNSAT. The encoding naturally
        // collapses to `WPBSum{} >= 1_i` (i.e. `0 ≥ 1`), so we let
        // define_proof_model run unchanged and install a contradiction
        // initialiser instead of the regular propagator.
        _has_no_values = true;
    }

    return true;
}

auto In::define_proof_model(ProofModel & model, const State &) -> void
{
    WPBSum sum;

    for (const auto & v : _val_vals)
        if (! is_literally_false(_var == v))
            sum += 1_i * (_var == v);

    // For each non-constant V_i, fully reify three flags, named and oriented as
    // cake_pb_cp's cencode_in does it -- which is literally cake's count helper
    // (cencode_count_aux), so this is the same encoding Count was conformed to
    // in #354:
    //   x[id][i][ge] ⇔ V_i ≥ var
    //   x[id][i][le] ⇔ V_i ≤ var
    //   x[id][i][eq] ⇔ ge ∧ le   (i.e. V_i = var)
    // The solver used to reify the strict complements (lt ⇔ var < V_i, gt ⇔ var
    // > V_i, sel ⇔ ¬lt ∧ ¬gt); ge = ¬gt and le = ¬lt exactly, so the selector
    // means what it always did, which is all the propagator ever references.
    for (const auto & [idx, V] : enumerate(_var_vals)) {
        vector<long long> pos{static_cast<long long>(idx)};
        auto ge = model.create_proof_flag_fully_reifying(_constraint_id, pos, "ge", WPBSum{} + 1_i * V + -1_i * _var >= 0_i);
        auto le = model.create_proof_flag_fully_reifying(_constraint_id, pos, "le", WPBSum{} + 1_i * V + -1_i * _var <= 0_i);
        auto sel = model.create_proof_flag_fully_reifying(_constraint_id, pos, "eq", WPBSum{} + 1_i * ge + 1_i * le >= 2_i);
        _selectors.push_back(sel);

        sum += 1_i * sel;
    }

    // cake labels the disjunction c[id][al1] (cat_least_one).
    model.add_labelled_constraint(_constraint_id, "al1", sum >= 1_i);
}

auto In::install_propagators(Propagators & propagators) -> void
{
    if (_has_no_values) {
        propagators.install_initial_contradiction(constraint_id(), constraint_type(),
            "An In constraint was posted with no values for its variable to take", JustifyUsingRUP{hints::In{constraint_id()}});
        return;
    }

    Triggers triggers;
    triggers.on_change.emplace_back(_var);
    for (const auto & V : _var_vals)
        triggers.on_change.emplace_back(V);

    // The permitted values as intervals, built once: the set is fixed for the
    // life of the constraint, and step 1 below takes the domain's difference
    // against it on every call. insert_at_end needs them ascending, which holds
    // because prepare() sorts and uniques _val_vals (and folds in any constant
    // members) and runs before this -- see constraint.cc.
    IntervalSet<Integer> val_vals_set;
    for (const auto & v : _val_vals)
        val_vals_set.insert_at_end(v);

    // A range can be said about any of these variables, whatever kind they are.
    // A registered view owns its range literals over its own encoded variable,
    // linked to the underlying one (#904), which is also the representation the
    // model states In's rows in -- so the conclusions, the reason literals and
    // the selector clauses below all name literals that exist, and the two bound
    // lemmas cross on whichever encoding each operand resolves to. A variable
    // with no bits encoding is the one thing that has no range literal, and that
    // is the proof layer's business rather than this propagator's: the logger
    // expands such a conclusion back to one line per value on its way out
    // (ProofLogger::infer, infer_explicitly).
    //
    // A width-one run stays per-value below, but for an unrelated reason:
    // not_in_range canonicalises to the same != literal there, so the range form
    // would buy nothing and cost two bound lemmas per source.

    propagators.install(
        constraint_id(),
        [var = _var, var_vals = _var_vals, val_vals = _val_vals, val_vals_set = move(val_vals_set), selectors = _selectors, owner = constraint_id()](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // Step 1: filter dom(var) — drop any value that no source supports.
            if (var_vals.empty()) {
                // The initial-domain shape (create_integer_variable(vector) posts In
                // over constants): each contiguous run of unsupported values is one
                // interval conclusion, RUP with no reason since asserting var in
                // [lo, hi] walks the order chain past every supported value into the
                // at-least-one.
                //
                // The conclusions were already interval-level; what was per-value was
                // finding them, by walking the domain and grouping maximal runs. The
                // runs a merge against the permitted set yields are the same
                // intervals: a run breaks exactly where the domain has a hole or a
                // permitted value intervenes, which is where each_interval_minus ends
                // one too. So this emits the identical inferences and changes nothing
                // in the proof -- it just stops taking O(|D(var)|) to find them.
                //
                // The copy has to be a named local, and so does the permitted set:
                // each_interval_minus() hands out a generator borrowing both, which
                // must outlive it (see IntervalSet's class documentation). It also
                // means the domain may be modified as we go, which the old code
                // needed a separate collection pass to allow.
                auto var_values = state.copy_of_values(var);
                for (auto [lo, hi] : var_values.each_interval_minus(val_vals_set))
                    inference.infer_not_in_range(logger, var, lo, hi, JustifyUsingRUP{hints::In{owner}}, NoReason{});
            }
            else {
                // The same difference, against a wider set. A value of var
                // survives if any permitted constant holds it or any source's
                // domain does, so what has to go is dom(var) minus the union of
                // val_vals_set and the sources' domains -- and the union is
                // built by erasing each piece from a copy of dom(var) in turn,
                // which costs the intervals involved and never a value (#874).
                // The old form asked the question the other way round, walking
                // dom(var) and testing each value for support, which took
                // O(|D(var)|) even when every value was supported and nothing
                // came out.
                //
                // Copies, and named ones, for two reasons: each_interval() hands
                // out a generator borrowing the set, which must outlive it (see
                // IntervalSet's class documentation), and the inferences below
                // modify the domains as they go.
                auto unsupported = state.copy_of_values(var);
                for (auto [lo, hi] : val_vals_set.each_interval())
                    unsupported.erase_range(lo, hi);
                for (const auto & V : var_vals) {
                    if (unsupported.empty())
                        break;
                    auto v_values = state.copy_of_values(V);
                    for (auto [lo, hi] : v_values.each_interval())
                        unsupported.erase_range(lo, hi);
                }

                LargeDomainIterationCounter unsupported_guard{"the number of values one In unsupported-value pruning has walked"};

                for (auto [run_lo, run_hi] : unsupported.each_interval()) {
                    if (run_lo < run_hi) {
                        Reason reason;
                        if (inference.want_reasons()) {
                            ReasonLiterals lits;
                            for (const auto & V : var_vals)
                                lits.emplace_back(not_in_range(V, run_lo, run_hi));
                            reason = ExplicitReason{std::move(lits)};
                        }

                        inference.infer_not_in_range(logger, var, run_lo, run_hi,
                            JustifyExplicitly{//
                                [logger, var, lo = run_lo, hi = run_hi, &var_vals, &selectors](const ReasonLiterals & reason) {
                                    for (const auto & [j, V] : enumerate(var_vals)) {
                                        // The range literal never crosses the equality;
                                        // only single bounds do. var >= lo crosses to
                                        // V >= lo under the selector, V's own range
                                        // literal steps from there to V >= hi + 1 by its
                                        // reverse reification, and that crosses back to
                                        // var >= hi + 1 -- so the two ge-layer lemmas are
                                        // all that is owed here.
                                        justify_not_in_range_across_equality(*logger, reason, var, lo, hi, V, lo, hi, selectors[j]);
                                        // Which makes this RUP, and this is what makes the
                                        // conclusion RUP: under the reason it unit
                                        // propagates ~sel_j, and with every selector out
                                        // and every permitted constant outside [lo, hi],
                                        // the at-least-one row has nothing left.
                                        logger->emit_rup_proof_line_under_reason(reason,
                                            WPBSum{} + 1_i * ! selectors[j] + 1_i * not_in_range(var, lo, hi) + 1_i * in_range(V, lo, hi) >= 1_i,
                                            ProofLevel::Temporary);
                                    }
                                },
                                ThenRUP::Yes, hints::InNotInRange{{owner}}},
                            reason);
                        continue;
                    }

                    // The per-value path. It is not State's own iterator any
                    // more, so it carries its own counter for the large-domain
                    // guard, in the same way as abs.cc's and element.cc's
                    // (issues #855, #875).
                    for (Integer v = run_lo; v <= run_hi; ++v) {
                        unsupported_guard.step();
                        if (! state.in_domain(var, v))
                            continue;

                        Reason reason;
                        if (inference.want_reasons()) {
                            ReasonLiterals lits;
                            for (const auto & V : var_vals)
                                lits.emplace_back(V != v);
                            reason = ExplicitReason{std::move(lits)};
                        }

                        inference.infer_not_equal(logger, var, v,
                            JustifyExplicitly{//
                                [logger, var, v, &selectors](const ReasonLiterals & reason) {
                                    for (const auto & sel : selectors)
                                        logger->emit_rup_proof_line_under_reason(
                                            reason, WPBSum{} + 1_i * ! sel + 1_i * (var != v) >= 1_i, ProofLevel::Temporary);
                                },
                                ThenRUP::Yes, hints::In{owner}},
                            reason);
                    }
                }
            }

            // Step 2: identify which V_i's still have any value in dom(var).
            // domains_intersect walks the two interval sets in merge order and
            // stops at the first overlap; the old any_of asked the same question
            // by walking dom(V) a value at a time, which for a wide V was the
            // whole domain whenever the answer was no (#874).
            optional<size_t> support_1, support_2;
            for (const auto & [i, V] : enumerate(var_vals)) {
                if (state.domains_intersect(V, var)) {
                    if (! support_1)
                        support_1 = i;
                    else {
                        support_2 = i;
                        break;
                    }
                }
            }

            // Does any constant in val_vals lie in dom(var)?
            bool const_supports = any_of(val_vals, [&](Integer c) { return state.in_domain(var, c); });

            // Step 3: if no constant supports and exactly one V_i supports, that V_i must
            // equal var, so prune V_i to dom(var).
            if (! const_supports && support_1 && ! support_2) {
                size_t i = *support_1;
                const auto & V = var_vals[i];

                // What V loses is its domain minus dom(var), and each contiguous
                // run of that is one conclusion. Merging the two interval sets
                // finds those runs directly; the old form walked dom(V) a value
                // at a time to find them, which was O(|D(V)|) however few came
                // out (#874). Named locals: each_interval_minus() borrows both
                // sets, and V's domain moves under us as the pruning lands.
                auto v_values = state.copy_of_values(V);
                auto var_values = state.copy_of_values(var);

                // var stays a declarative generic_reason (its domain walk is
                // deferred and skipped when no reason is read); only the cross-
                // product of supporting-selector literals is the explicit extra,
                // and the whole build is guarded. It is the same reason for every
                // run -- nothing in it mentions what is being removed -- so it is
                // assembled once rather than per conclusion.
                //
                // One literal per source per *interval* of dom(var) where a range
                // can be said at all. The per-value spelling made both this and
                // the scaffolding below O(var_vals x |D(var)|), which the guard
                // does not see (a reason is only materialised with proofs on) and
                // the audit lane does not run -- but the proof-scaling survey
                // does, and it showed the single-support rule's proof growing
                // tenfold per decade of width after the propagation had stopped
                // doing so (#874).
                bool want_reason = inference.want_reasons();
                Reason reason;
                if (want_reason) {
                    ReasonLiterals extra;
                    for (const auto & [j, V_j] : enumerate(var_vals)) {
                        if (j == i)
                            continue;
                        for (auto [a, b] : var_values.each_interval())
                            extra.emplace_back(not_in_range(V_j, a, b));
                    }
                    reason = with_extra(generic_reason(vector{var}), std::move(extra));
                }

                // Every other source is missing all of dom(var), so its selector
                // must be false; the at-least-one row is then down to V's own
                // selector, which is what pins V to var for the lemmas below.
                // Value-independent, so it is emitted once per conclusion rather
                // than once per removed value.
                auto rule_out_other_selectors = [logger, &state, &var_vals, &selectors, &var_values, var, i](const ReasonLiterals & reason) {
                    // When var is fixed, dom(var) is a single value and the inner-loop
                    // scaffolding line `! sel_j + (var != w)` collapses (under the reason's
                    // `var = w` literal) to the same constraint as the outer `! sel_j`, so
                    // skip the inner loop entirely.
                    bool var_fixed = state.has_single_value(var);
                    for (const auto & [j, V_j] : enumerate(var_vals)) {
                        if (j == i)
                            continue;
                        if (! var_fixed) {
                            // `! sel_j` follows from dom(var) being emptied of
                            // anything V_j could be, one interval at a time: the
                            // reason's lower bound plus the first interval's
                            // exclusion gives var past it, the hole after it is a
                            // reason literal that steps over the gap, and so on
                            // until the walk passes the reason's upper bound.
                            // Which is the same walk as step 1's, and needs the
                            // same two lemmas to cross the selector's equality
                            // -- for the same reason, and only where the run is
                            // wider than one value.
                            for (auto [a, b] : var_values.each_interval()) {
                                if (a < b)
                                    justify_not_in_range_across_equality(*logger, reason, var, a, b, V_j, a, b, selectors[j]);
                                logger->emit_rup_proof_line_under_reason(reason,
                                    WPBSum{} + 1_i * ! selectors[j] + 1_i * not_in_range(var, a, b) + 1_i * in_range(V_j, a, b) >= 1_i,
                                    ProofLevel::Temporary);
                            }
                        }
                        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * ! selectors[j] >= 1_i, ProofLevel::Temporary);
                    }
                };

                LargeDomainIterationCounter support_guard{"the number of values one In single-support pruning has walked"};

                for (auto [run_lo, run_hi] : v_values.each_interval_minus(var_values)) {
                    if (run_lo < run_hi) {
                        // With the other selectors ruled out, V = var is forced,
                        // and the two ge-layer lemmas carry the run's endpoints
                        // across that equality -- the mirror of step 1, which
                        // carries them the other way under a selector that is not
                        // yet decided. The reason gains the run it is about;
                        // with_extra copies its base, so each conclusion gets a
                        // fresh one rather than an accumulating literal.
                        inference.infer_not_in_range(logger, V, run_lo, run_hi,
                            JustifyExplicitly{//
                                [&, lo = run_lo, hi = run_hi](const ReasonLiterals & reason) {
                                    rule_out_other_selectors(reason);
                                    justify_not_in_range_across_equality(*logger, reason, V, lo, hi, var, lo, hi);
                                },
                                ThenRUP::Yes, hints::InNotInRange{{owner}}},
                            want_reason ? with_extra(reason, ReasonLiterals{not_in_range(var, run_lo, run_hi)}) : Reason{});
                        continue;
                    }

                    for (Integer val = run_lo; val <= run_hi; ++val) {
                        support_guard.step();
                        if (! state.in_domain(V, val))
                            continue;

                        inference.infer_not_equal(logger, V, val,
                            JustifyExplicitly{//
                                [&](const ReasonLiterals & reason) { rule_out_other_selectors(reason); }, ThenRUP::Yes, hints::In{owner}},
                            reason);
                    }
                }
            }

            // If var is fixed to a constant we know is in val_vals, no further propagation
            // can possibly fire usefully.
            auto fixed = state.optional_single_value(var);
            if (fixed && binary_search(val_vals, *fixed))
                return PropagatorState::DisableUntilBacktrack;

            return PropagatorState::Enable;
        },
        triggers);
}

auto In::constraint_type() const -> std::string
{
    return "in";
}

auto In::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    vector<SExpr> vals;
    for (const auto & v : _var_vals)
        vals.push_back(tracker.s_expr_term_of(v));
    for (const auto & v : _val_vals)
        vals.push_back(SExpr::atom(v.to_string()));
    // cake_pb_cp's `in` parser takes the candidate list first, then the
    // variable: (id in (values...) var). Emit that order so the workflow-2
    // re-derivation parses (it rejects the variable-first form outright).
    return SExpr::list(
        {SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(std::move(vals)), tracker.s_expr_term_of(_var)});
}
