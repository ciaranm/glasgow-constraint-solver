#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/innards/justify_not_in_range.hh>
#include <gcs/constraints/min_max/hints.hh>
#include <gcs/constraints/min_max/min_max.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>

#include <util/enumerate.hh>

#include <sstream>

#include <algorithm>
#include <sstream>
#include <string>

using namespace gcs;
using namespace gcs::innards;

using std::nullopt;
using std::optional;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;
using std::ranges::any_of;

ArrayMinMax::ArrayMinMax(vector<IntegerVariableID> vars, const IntegerVariableID result, bool min) : _vars(move(vars)), _result(result), _min(min)
{
}

auto ArrayMinMax::clone() const -> unique_ptr<Constraint>
{
    return make_unique<ArrayMinMax>(_vars, _result, _min);
}

auto ArrayMinMax::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto ArrayMinMax::prepare(Propagators &, State &, ProofModel * const) -> bool
{
    if (_vars.empty())
        throw InvalidProblemDefinitionException{"not sure how min and max are defined over an empty array"};
    return true;
}

auto ArrayMinMax::define_proof_model(ProofModel & model) -> void
{
    // (for min) each var >= result, i.e. var - result >= 0
    for (const auto & v : _vars) {
        model.add_constraint(WPBSum{} + (_min ? 1_i : -1_i) * v + (_min ? -1_i : 1_i) * _result >= 0_i, nullopt);
    }

    WPBSum al1_selector;

    // (for min) f_i <-> var[i] <= result, i.e. var - result <= 0. Name the
    // selector x[id][i] (the position-indexed two-level form) so it matches
    // cake_pb_cp's per-value selector by name -- the propagator's RUP steps
    // reference it, so workflow-2 enumeration needs the names to agree.
    for (const auto & [id, var] : enumerate(_vars)) {
        auto selector = model.create_proof_flag(_constraint_id, std::vector<long long>{static_cast<long long>(id)});
        _selectors.push_back(selector);
        model.add_constraint(WPBSum{} + (_min ? 1_i : -1_i) * var + (_min ? -1_i : 1_i) * _result <= 0_i, {{selector}});
        model.add_constraint(WPBSum{} + (_min ? 1_i : -1_i) * var + (_min ? -1_i : 1_i) * _result >= 1_i, {{! selector}});
        al1_selector += 1_i * selector;
    }

    // sum f_i >= 1
    model.add_constraint(al1_selector >= 1_i);
}

auto ArrayMinMax::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers{.on_change = {_result}};
    for (const auto & v : _vars)
        triggers.on_change.emplace_back(v);

    propagators.install(
        constraint_id(),
        [vars = _vars, result = _result, min = _min, selectors = _selectors, owner = constraint_id()](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // result <= upper bound of each vars
            for (auto & var : vars) {
                auto var_bounds = state.bounds(var);
                if (min)
                    inference.infer_less_than(logger, result, var_bounds.second + 1_i, JustifyUsingRUP{hints::MinMax{owner}},
                        ExplicitReason{ReasonLiterals{{var <= var_bounds.second}}});
                else
                    inference.infer_greater_than_or_equal(logger, result, var_bounds.first, JustifyUsingRUP{hints::MinMax{owner}},
                        ExplicitReason{ReasonLiterals{{var >= var_bounds.first}}});
            }

            // each var >= result
            auto result_bounds = state.bounds(result);
            for (auto & var : vars) {
                if (min)
                    inference.infer_greater_than_or_equal(logger, var, result_bounds.first, JustifyUsingRUP{hints::MinMax{owner}},
                        ExplicitReason{ReasonLiterals{{result >= result_bounds.first}}});
                else
                    inference.infer_less_than(logger, var, state.upper_bound(result) + 1_i, JustifyUsingRUP{hints::MinMax{owner}},
                        ExplicitReason{ReasonLiterals{{result <= result_bounds.second}}});
            }

            // result in union(vars)
            for (auto value : state.each_value_mutable(result)) {
                bool found_support = false;
                for (auto & var : vars) {
                    if (state.in_domain(var, value)) {
                        found_support = true;
                        break;
                    }
                }

                if (! found_support) {
                    ReasonLiterals reason;
                    for (auto & var : vars)
                        reason.emplace_back(var != value);

                    inference.infer_not_equal(logger, result, value,
                        JustifyExplicitly{//
                            [logger, result, value, &selectors](const ReasonLiterals & reason) {
                                // show that none of the selectors work, if we're taking the result to be that value and also
                                // that the value is missing from all of the vars
                                for (const auto & sel : selectors)
                                    logger->emit_rup_proof_line_under_reason(
                                        reason, WPBSum{} + (1_i * ! sel) + (1_i * (result != value)) >= 1_i, ProofLevel::Temporary);
                            },
                            ThenRUP::Yes, hints::MinMax{owner}},
                        ExplicitReason{reason});
                }
            }

            // is there more than one variable that can support the values in result?
            optional<IntegerVariableID> support_1, support_2;
            for (auto & var : vars) {
                if (any_of(state.each_value_immutable(result), [&](const Integer & val) { return state.in_domain(var, val); })) {
                    if (! support_1)
                        support_1 = var;
                    else {
                        support_2 = var;
                        break;
                    }
                }
            }

            if (! support_1)
                throw UnexpectedException{"missing support, bug in MinMaxArray propagator"};
            else if (! support_2) {
                // no, there's only a single var left that has any intersection with result. so, that
                // variable has to lose any values not present in result.
                // generic_reason over result stays declarative; the per-var support
                // literals are the explicit extra, and the whole O(vars x dom(result))
                // base is assembled only when a reason will be read.
                bool want_reason = inference.want_reasons();
                Reason reason;
                if (want_reason) {
                    ReasonLiterals extra;
                    for (auto & var : vars) {
                        if (var == *support_1)
                            continue;
                        for (const auto & val : state.each_value_immutable(result))
                            extra.emplace_back(var != val);
                    }
                    reason = with_extra(generic_reason(vector{result}), std::move(extra));
                }

                auto support_1_set = state.copy_of_values(*support_1);
                auto result_set = state.copy_of_values(result);

                // The selector can only be true for the supporting variable: every other var
                // is missing all of result's values, so its model selector must be false. This
                // is value-independent, so the range path emits it once per interval rather
                // than once per removed value.
                auto rule_out_other_selectors = [&](const ReasonLiterals & reason) {
                    for (const auto & [idx, var] : enumerate(vars))
                        if (var != *support_1) {
                            for (const auto & rval : state.each_value_immutable(result))
                                logger->emit_rup_proof_line_under_reason(
                                    reason, WPBSum{} + (1_i * ! selectors.at(idx)) + (1_i * (result != rval)) >= 1_i, ProofLevel::Temporary);
                            logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + (1_i * ! selectors.at(idx)) >= 1_i, ProofLevel::Temporary);
                        }
                };

                // Each contiguous removed interval is a single ~[support_1 in lo..hi]
                // conclusion. With the other selectors ruled out, al1 forces support_1's
                // selector true, so the model pins support_1 == result; two ge-layer bound
                // lemmas then bridge result's absence from [lo, hi] across that equality,
                // exactly as in equals.cc (the range literal asserts order atoms, never bits,
                // so the conclusion is not RUP without them). Views and constants, where the
                // bridge does not apply, keep the per-value path.
                auto both_simple = std::holds_alternative<SimpleIntegerVariableID>(IntegerVariableID{*support_1}) &&
                    std::holds_alternative<SimpleIntegerVariableID>(IntegerVariableID{result});

                for (auto [lo, hi] : support_1_set.each_interval_minus(result_set)) {
                    if (both_simple) {
                        // The support reason is the base reason plus the just-excluded
                        // interval; with_extra copies the base, so each interval gets a
                        // fresh reason rather than an accumulating literal.
                        inference.infer_not_in_range(logger, *support_1, lo, hi,
                            JustifyExplicitly{//
                                [&, lo = lo, hi = hi](const ReasonLiterals & reason) {
                                    rule_out_other_selectors(reason);
                                    justify_not_in_range_across_equality(
                                        *logger, reason, std::get<SimpleIntegerVariableID>(IntegerVariableID{*support_1}), lo, hi, result, lo, hi);
                                },
                                ThenRUP::Yes, hints::MinMax{owner}},
                            want_reason ? with_extra(reason, ReasonLiterals{not_in_range(result, lo, hi)}) : Reason{});
                    }
                    else
                        for (Integer val = lo; val <= hi; ++val)
                            inference.infer(logger, *support_1 != val,
                                JustifyExplicitly{//
                                    [&, val = val](const ReasonLiterals & reason) {
                                        rule_out_other_selectors(reason);
                                        // now fish out the supporting variable, and show that it has to have its selector true
                                        for (const auto & [idx, var] : enumerate(vars))
                                            if (var == *support_1)
                                                logger->emit_rup_proof_line_under_reason(reason,
                                                    WPBSum{} + (1_i * (*support_1 == val)) + (1_i * selectors.at(idx)) >= 1_i, ProofLevel::Temporary);
                                    },
                                    ThenRUP::Yes, hints::MinMax{owner}},
                                reason);
                }
            }

            // Full GAC on the array variables. The rules above keep every var
            // within result's bounds and every result value reachable as the
            // extremum, but a var can still hold an interior value that can be
            // neither the extremum itself nor sit under an extremum that some
            // *other* var provides. For Max, value v of var_i is supported iff
            // either v is itself a feasible result (v in D(result), and every
            // other var can be <= v, i.e. v >= the largest other lower bound),
            // or some other var can provide a larger result value (an r in
            // D(result), r > v, reachable by another var that can also sit at or
            // above the largest other lower bound). Min is the mirror image.
            //
            // Proof of var_i != v: the result-bound rule above already left
            // D(result) inside [max lower bound, +inf), so every result value r
            // strictly past v has r >= L_{-i}; by other_extreme's definition no
            // *other* var can then equal r, and var_i = v can't either, so the
            // al1 "result is one of the values" selector constraint is violated.
            // Ruling out every such r forces result onto the wrong side of v,
            // contradicting result >= var_i (for Max). A pure selector argument,
            // no cross-variable bound reasoning needed.
            {
                vector<IntegerVariableID> scope = vars;
                scope.push_back(result);
                for (const auto & [i, var_i] : enumerate(vars)) {
                    optional<Integer> others_limit; // max: largest other lower bound; min: smallest other upper bound
                    for (const auto & [k, var_k] : enumerate(vars)) {
                        if (k == i)
                            continue;
                        auto bk = state.bounds(var_k);
                        auto lim = min ? bk.second : bk.first;
                        others_limit = ! others_limit ? lim : (min ? std::min(*others_limit, lim) : std::max(*others_limit, lim));
                    }
                    optional<Integer> other_extreme; // extremal result value some other var can provide
                    for (auto r : state.each_value_immutable(result)) {
                        if (others_limit && (min ? r > *others_limit : r < *others_limit))
                            continue;
                        bool other_has = false;
                        for (const auto & [k, var_k] : enumerate(vars))
                            if (k != i && state.in_domain(var_k, r)) {
                                other_has = true;
                                break;
                            }
                        if (other_has)
                            other_extreme = ! other_extreme ? r : (min ? std::min(*other_extreme, r) : std::max(*other_extreme, r));
                    }
                    for (auto v : state.each_value_mutable(var_i)) {
                        bool supported_as_extreme = state.in_domain(result, v) && (! others_limit || (min ? v <= *others_limit : v >= *others_limit));
                        bool supported_under_other = other_extreme && (min ? v > *other_extreme : v < *other_extreme);
                        if (! supported_as_extreme && ! supported_under_other) {
                            auto justf = [&, var_i = var_i, v = v](const ReasonLiterals & reason) {
                                for (auto r : state.each_value_immutable(result)) {
                                    if (min ? r >= v : r <= v)
                                        continue;
                                    // if var_i = v and result = r, no var can equal result, breaking al1
                                    for (std::size_t k = 0; k < vars.size(); ++k)
                                        logger->emit_rup_proof_line_under_reason(reason,
                                            WPBSum{} + 1_i * (var_i != v) + 1_i * (result != r) + 1_i * (! selectors.at(k)) >= 1_i,
                                            ProofLevel::Temporary);
                                    logger->emit_rup_proof_line_under_reason(
                                        reason, WPBSum{} + 1_i * (var_i != v) + 1_i * (result != r) >= 1_i, ProofLevel::Temporary);
                                }
                            };
                            inference.infer_not_equal(
                                logger, var_i, v, JustifyExplicitly{justf, ThenRUP::Yes, hints::MinMax{owner}}, generic_reason(scope));
                        }
                    }
                }
            }

            return PropagatorState::Enable;
        },
        triggers);
}

auto ArrayMinMax::s_expr(const innards::ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    std::vector<SExpr> vars;
    for (const auto & v : _vars)
        vars.push_back(tracker.s_expr_term_of(v));
    // cake_pb_cp's array aggregate keyword is array_min / array_max with shape
    // (id array_min (Xs) Y); a bare min / max is its *binary* op (X op Y = Z).
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom(_min ? "array_min" : "array_max"), SExpr::list(std::move(vars)),
        tracker.s_expr_term_of(_result)});
}

Min::Min(const IntegerVariableID v1, const IntegerVariableID v2, const IntegerVariableID result) : ArrayMinMax({v1, v2}, result, true)
{
}

Max::Max(const IntegerVariableID v1, const IntegerVariableID v2, const IntegerVariableID result) : ArrayMinMax({v1, v2}, result, false)
{
}

ArrayMin::ArrayMin(vector<IntegerVariableID> vars, const IntegerVariableID result) : ArrayMinMax(move(vars), result, true)
{
}

ArrayMax::ArrayMax(vector<IntegerVariableID> vars, const IntegerVariableID result) : ArrayMinMax(move(vars), result, false)
{
}
