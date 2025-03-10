#include <gcs/constraints/among.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/recover_am1.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <algorithm>
#include <map>
#include <optional>
#include <sstream>
#include <string>
#include <tuple>

using namespace gcs;
using namespace gcs::innards;

using std::make_optional;
using std::make_shared;
using std::map;
using std::optional;
using std::pair;
using std::shared_ptr;
using std::string;
using std::stringstream;
using std::to_string;
using std::tuple;
using std::unique_ptr;
using std::vector;
using std::ranges::distance;
using std::ranges::empty;
using std::ranges::none_of;
using std::ranges::subrange;

namespace
{
    auto uniqueify(const vector<Integer> & v) -> vector<Integer>
    {
        auto result = v;
        sort(result.begin(), result.end());
        result.erase(unique(result.begin(), result.end()), result.end());
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

auto Among::install(Propagators & propagators, State &, ProofModel * const optional_model) && -> void
{
    // we only care about the bounds for how_many, but we care about any deletions for the
    // rest of the variables
    Triggers triggers;
    triggers.on_change.insert(triggers.on_change.end(), _vars.begin(), _vars.end());
    triggers.on_bounds.emplace_back(_how_many);

    pair<optional<ProofLine>, optional<ProofLine>> sum_line;
    if (optional_model) {
        // very easy PB encoding: sum up over the condition that each variable equals one of the
        // value of interest options, and make that equal the how many variable.
        WeightedPseudoBooleanSum sum;
        for (auto & var : _vars)
            for (auto & val : _values_of_interest)
                sum += 1_i * (var == val);
        sum_line = optional_model->add_constraint("Among", "how many", sum == 1_i * _how_many);
    }

    // for proof logging, we're going to need at-most-one constraints over the
    // values of interest for each variable. compute these once and remember
    // them.
    auto am1_lines = make_shared<map<IntegerVariableID, ProofLine>>();
    propagators.install_initialiser([vars = _vars, values_of_interest = _values_of_interest, am1_lines = am1_lines](
                                        const State &, auto &, ProofLogger * const logger) -> void {
        if (logger && values_of_interest.size() > 1) {
            for (auto & var : vars) {
                vector<IntegerVariableCondition> var_eq_vois;
                for (const auto & voi : values_of_interest)
                    var_eq_vois.push_back(var != voi);
                am1_lines->emplace(var, recover_am1<IntegerVariableCondition>(*logger, ProofLevel::Top, var_eq_vois, [&](const IntegerVariableCondition & a, const IntegerVariableCondition & b) {
                    logger->emit_proof_comment("among am1 recover follows");
                    return logger->emit(RUPProofRule{}, WeightedPseudoBooleanSum{} + 1_i * a + 1_i * b >= 1_i, ProofLevel::Temporary);
                }));
            }
        }
    });

    propagators.install(
        [vars = _vars, values_of_interest = _values_of_interest, how_many = _how_many, sum_line = sum_line, am1_lines = am1_lines](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // partition variables to be 1) those that must not match, 2) those that must match, and 3) those
            // where they might match but don't have to.
            vector<IntegerVariableID> partitioned_vars = vars;
            auto not_impossible_start = partition(partitioned_vars.begin(), partitioned_vars.end(), [&](const auto & var) -> bool {
                return none_of(values_of_interest, [&](const auto & val) -> bool { return state.in_domain(var, val); });
            });
            auto can_be_either_start = partition(not_impossible_start, partitioned_vars.end(), [&](const auto & var) -> bool {
                return none_of(state.each_value_immutable(var), [&](const auto & val) -> bool {
                    return values_of_interest.end() == find(values_of_interest.begin(), values_of_interest.end(), val);
                });
            });

            auto must_not_match_vars = subrange{partitioned_vars.begin(), not_impossible_start};
            auto must_match_vars = subrange{not_impossible_start, can_be_either_start};
            auto can_be_either_vars = subrange{can_be_either_start, partitioned_vars.end()};
            auto can_be_either_or_must_vars = subrange{not_impossible_start, partitioned_vars.end()};

            auto must_not_match_count = Integer(distance(must_not_match_vars));
            auto must_match_count = Integer(distance(must_match_vars));
            auto can_be_either_count = Integer(distance(can_be_either_vars));

            // we now know how many variables definitely match, and how
            // many can't match, so we can derive bounds on the how many
            // variable.
            auto vars_reason = generic_reason(state, vars);
            inference.infer(logger, how_many >= must_match_count, JustifyUsingRUP{}, vars_reason);
            auto less_than_this_many = Integer(vars.size()) - must_not_match_count + 1_i;
            inference.infer(logger, how_many < less_than_this_many, JustifyExplicitly{[&](const Reason &) -> void {
                // for any variable that isn't ruled out, show that it can contribute at
                // most one to the count.
                if (sum_line.second && ! empty(can_be_either_or_must_vars) && values_of_interest.size() > 1) {
                    stringstream line;
                    line << "pol " << *sum_line.second;
                    for (const auto & var : can_be_either_or_must_vars)
                        line << " " << am1_lines->at(var) << " +";
                    logger->emit_proof_line(line.str(), ProofLevel::Temporary);
                }
            }},
                vars_reason);

            // potentially now we know that any undecided variables must actually be either
            // matching or not matching.
            auto [at_least_how_many, at_most_how_many] = state.bounds(how_many);

            auto vars_and_bounds_reason = [&vars_reason, how_many, at_least_how_many, at_most_how_many]() {
                auto result = vars_reason();
                result.push_back(how_many >= at_least_how_many);
                result.push_back(how_many < at_most_how_many + 1_i);
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
                for (const auto & var : vars) {
                    bool all_match = true;
                    for (const auto & val : state.each_value_immutable(var))
                        if (values_of_interest.end() == find(values_of_interest.begin(), values_of_interest.end(), val))
                            all_match = false;

                    if (! all_match) {
                        vector<Literal> inferences;
                        for (const auto & val : values_of_interest)
                            inferences.push_back(var != val);

                        inference.infer_all(logger, inferences, JustifyExplicitly{[&](const Reason &) -> void {
                            // for any variable that is forced, show that it can contribute at
                            // most one to the count
                            if (sum_line.second && ! empty(must_match_vars) && values_of_interest.size() > 1) {
                                stringstream line;
                                line << "pol " << *sum_line.second;
                                for (const auto & var : must_match_vars)
                                    line << " " << am1_lines->at(var) << " +";
                                logger->emit_proof_line(line.str(), ProofLevel::Temporary);
                            }
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
                    for (const auto & var : vars) {
                        bool might_match = false;
                        for (const auto & val : values_of_interest) {
                            if (state.in_domain(var, val)) {
                                might_match = true;
                                break;
                            }
                        }

                        if (might_match)
                            for (const auto & val : state.each_value_mutable(var))
                                if (values_of_interest.end() == find(values_of_interest.begin(), values_of_interest.end(), val)) {
                                    inference.infer(logger, var != val, JustifyExplicitly{[&](const Reason &) {
                                        // need to point out that if var == val then var != voi for each voi
                                        for (const auto & voi : values_of_interest)
                                            logger->emit(RUPProofRule{}, WeightedPseudoBooleanSum{} + 1_i * (var != val) + 1_i * (var != voi) >= 1_i, ProofLevel::Temporary);

                                        // now each other variable that may or may not match is contributing at most one to the sum
                                        if (sum_line.second && values_of_interest.size() > 1) {
                                            stringstream line;
                                            line << "pol " << *sum_line.second;
                                            for (const auto & other_var : can_be_either_vars)
                                                if (var != other_var)
                                                    line << " " << am1_lines->at(other_var) << " +";
                                            logger->emit_proof_line(line.str(), ProofLevel::Temporary);
                                        }
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
        triggers, "among");
}
