#include <gcs/constraints/among.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <algorithm>
#include <optional>
#include <sstream>
#include <string>

using namespace gcs;
using namespace gcs::innards;

using std::holds_alternative;
using std::optional;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;
using std::ranges::contains;
using std::ranges::none_of;
using std::ranges::sort;
using std::ranges::unique;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

namespace
{
    auto uniqueify(const vector<Integer> & v) -> vector<Integer>
    {
        auto result = v;
        sort(result);
        result.erase(unique(result).begin(), result.end());
        return result;
    }
}

Among::Among(vector<IntegerVariableID> vars, const vector<Integer> & values_of_interest, const IntegerVariableID & how_many) :
    _vars(move(vars)),
    _values_of_interest(uniqueify(values_of_interest)),
    _how_many(how_many)
{
}

auto Among::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Among>(_vars, _values_of_interest, _how_many);
}

auto Among::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto Among::define_proof_model(ProofModel & model) -> void
{
    // Conform to cake_pb_cp's encode_among (#354): per position i, a flag
    // x[id][i][al1] ⇔ (var_i takes a value in the set), i.e. ⇔ Σ_{v∈iS}(var_i = v) ≥ 1
    // (cake's at-least-one), then the sum of those flags == how_many, emitted as
    // cake's c[id][le] / c[id][ge] halves -- the same counting-family bitsum as
    // count / nvalue. (The solver previously summed every (var = val) literal in one
    // flat constraint; the per-position al1 flag is what cake and the propagator both
    // name, and a single Boolean per position is inherently ≤ 1, so the old
    // at-most-one scaffolding is no longer needed.)
    for (const auto & [i, var] : enumerate(_vars)) {
        WPBSum in_set;
        for (const auto & val : _values_of_interest)
            in_set += 1_i * (var == val);
        _flags.push_back(model.create_proof_flag_fully_reifying(_constraint_id,
            vector<long long>{static_cast<long long>(i)}, "al1", in_set >= 1_i));
    }

    WPBSum how_many_sum;
    for (const auto & flag : _flags)
        how_many_sum += 1_i * flag;
    how_many_sum += -1_i * _how_many;

    model.add_labelled_constraint(as_string(_constraint_id), "le", "ge",
        "Among", "sum of flags", how_many_sum == 0_i);
}

auto Among::install_propagators(Propagators & propagators) -> void
{
    // we only care about the bounds for how_many, but we care about any deletions for the
    // rest of the variables
    Triggers triggers;
    triggers.on_change.insert(triggers.on_change.end(), _vars.begin(), _vars.end());
    triggers.on_bounds.emplace_back(_how_many);

    propagators.install(
        constraint_id(),
        [vars = _vars, values_of_interest = _values_of_interest, how_many = _how_many, flags = _flags](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // Classify each variable: it must NOT match if its whole domain is disjoint
            // from the set; it must match if its whole domain lies inside the set;
            // otherwise it can be either. (A non-empty domain can be at most one of these.)
            auto domain_disjoint_from_set = [&](const IntegerVariableID & var) -> bool {
                return none_of(values_of_interest, [&](const auto & val) -> bool { return state.in_domain(var, val); });
            };
            auto domain_within_set = [&](const IntegerVariableID & var) -> bool {
                return none_of(state.each_value_immutable(var), [&](const auto & val) -> bool {
                    return ! contains(values_of_interest, val);
                });
            };

            auto must_not_match_count = 0_i, must_match_count = 0_i, can_be_either_count = 0_i;
            for (const auto & var : vars) {
                if (domain_disjoint_from_set(var))
                    ++must_not_match_count;
                else if (domain_within_set(var))
                    ++must_match_count;
                else
                    ++can_be_either_count;
            }

            // Pin the al1 flag of every must-match variable to 1: from the variable's
            // at-least-one-value axiom and the flag's reverse half (¬flag → no set value
            // taken). cake's c[id] sum then RUP-implies the lower bounds. (Constants are
            // folded into the sum's RHS, so they carry no flag of their own.)
            auto pin_must_match_flags = [&](const ReasonFunction & reason) -> void {
                for (const auto & [idx, var] : enumerate(vars))
                    if (domain_within_set(var) && ! holds_alternative<ConstantIntegerVariableID>(var)) {
                        // materialise the axiom so the RUP step below can use it
                        (void)logger->names_and_ids_tracker().need_constraint_saying_variable_takes_at_least_one_value(var);
                        logger->emit_rup_proof_line_under_reason(reason,
                            WPBSum{} + 1_i * flags[idx] >= 1_i, ProofLevel::Temporary);
                    }
            };
            // Pin the al1 flag of every must-not-match variable to 0: from the flag's
            // forward half (flag → some set value) against the disjoint domain. No
            // at-most-one lines are needed -- the al1 flag is already a single 0/1
            // contribution per position.
            auto pin_must_not_match_flags = [&](const ReasonFunction & reason) -> void {
                for (const auto & [idx, var] : enumerate(vars))
                    if (domain_disjoint_from_set(var))
                        logger->emit_rup_proof_line_under_reason(reason,
                            WPBSum{} + 1_i * (! flags[idx]) >= 1_i, ProofLevel::Temporary);
            };

            // we now know how many variables definitely match, and how
            // many can't match, so we can derive bounds on the how many
            // variable.
            auto vars_reason = generic_reason(state, vars);
            inference.infer(logger, how_many >= must_match_count,
                JustifyExplicitlyThenRUP{[&](const ReasonFunction & reason) -> void { pin_must_match_flags(reason); }},
                vars_reason);
            auto less_than_this_many = Integer(vars.size()) - must_not_match_count + 1_i;
            inference.infer(logger, how_many < less_than_this_many,
                JustifyExplicitlyThenRUP{[&](const ReasonFunction & reason) -> void { pin_must_not_match_flags(reason); }},
                vars_reason);

            // potentially now we know that any undecided variables must actually be either
            // matching or not matching.
            auto [at_least_how_many, at_most_how_many] = state.bounds(how_many);

            auto vars_and_bounds_reason = [&vars_reason, how_many, at_least_how_many, at_most_how_many]() {
                auto result = vars_reason();
                result.push_back(how_many >= at_least_how_many);
                result.push_back(how_many <= at_most_how_many);
                return result;
            };

            // if we have enough definitely matching values, nothing else can match
            if (must_match_count == at_most_how_many) {
                if (at_least_how_many != at_most_how_many) {
                    // in my head, this can only happen if we know exactly
                    // what the how many variable is set to, because
                    // otherwise we'd have some wiggle room.
                    throw UnexpectedException{"something's wrong, at_least_how_many != at_most_how_many option 1"};
                }

                // anything that might match actually mustn't match
                for (const auto & [idx_sb, var_sb] : enumerate(vars)) {
                    auto idx = idx_sb;
                    auto var = var_sb;
                    if (! domain_within_set(var)) {
                        vector<Literal> inferences;
                        for (const auto & val : values_of_interest)
                            inferences.push_back(var != val);

                        inference.infer_all(logger, inferences, JustifyExplicitlyThenRUP{[&](const ReasonFunction & reason) -> void {
                            // The count is fixed and the must-match variables already
                            // account for all of it, so this variable's al1 flag is 0 --
                            // hence it takes no set value, i.e. var ≠ every value of interest.
                            pin_must_match_flags(reason);
                            logger->emit_rup_proof_line_under_reason(reason,
                                WPBSum{} + 1_i * (! flags[idx]) >= 1_i, ProofLevel::Temporary);
                        }},
                            vars_and_bounds_reason);
                    }
                }

                // now every variable is set in a way that either must
                // match or must not match, and the count is fixed, so
                // we'll never propagate anything again
                return PropagatorState::DisableUntilBacktrack;
            }

            if (must_match_count + can_be_either_count == at_least_how_many) {
                if (at_least_how_many != at_most_how_many) {
                    // again, in my head, this can only happen if we know
                    // exactly what the how many variable is set to,
                    // because otherwise we'd have some wiggle room.
                    throw UnexpectedException{"something's wrong, at_least_how_many != at_most_how_many option 2"};
                }

                if (can_be_either_count > 0_i) {
                    // each that may or may not match must in fact match
                    for (const auto & [idx_sb, var_sb] : enumerate(vars)) {
                        auto idx = idx_sb;
                        auto var = var_sb;
                        bool might_match = false;
                        for (const auto & val : values_of_interest) {
                            if (state.in_domain(var, val)) {
                                might_match = true;
                                break;
                            }
                        }

                        if (might_match)
                            for (const auto & val : state.each_value_mutable(var))
                                if (! contains(values_of_interest, val)) {
                                    inference.infer(logger, var != val, JustifyExplicitlyThenRUP{[&](const ReasonFunction & reason) {
                                        // With the must-match flags pinned to 1 and the
                                        // must-not-match flags to 0, the fixed count forces
                                        // every can-be-either variable (a single 0/1 flag
                                        // each) to match, so this one's al1 flag is 1 --
                                        // hence it can't take the non-set value val.
                                        pin_must_match_flags(reason);
                                        pin_must_not_match_flags(reason);
                                        logger->emit_rup_proof_line_under_reason(reason,
                                            WPBSum{} + 1_i * flags[idx] >= 1_i, ProofLevel::Temporary);
                                        // if var == val (val ∉ set) then var ≠ each voi
                                        for (const auto & voi : values_of_interest)
                                            logger->emit_rup_proof_line_under_reason(reason,
                                                WPBSum{} + 1_i * (var != val) + 1_i * (var != voi) >= 1_i, ProofLevel::Temporary);
                                    }},
                                        vars_and_bounds_reason);
                                }
                    }

                    // now every variable is set in a way that either must
                    // match or must not match, and the count is fixed, so
                    // we'll never propagate anything again
                    return PropagatorState::DisableUntilBacktrack;
                }
            }

            return PropagatorState::Enable;
        },
        triggers);
}

auto Among::s_exprify(const ProofModel * const model) const -> std::string
{
    stringstream s;

    print(s, "{} among (", _constraint_id);
    for (const auto & var : _vars) {
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(var));
    }
    print(s, ") (");
    for (const auto & val : _values_of_interest) {
        print(s, " {}", val);
    }
    print(s, ") {}", model->names_and_ids_tracker().s_expr_name_of(_how_many));

    return s.str();
}
