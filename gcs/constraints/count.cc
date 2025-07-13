#include <gcs/constraints/count.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>

#include <optional>
#include <sstream>
#include <string>
#include <tuple>

using namespace gcs;
using namespace gcs::innards;

using std::make_optional;
using std::optional;
using std::pair;
using std::string;
using std::stringstream;
using std::tuple;
using std::unique_ptr;
using std::vector;

Count::Count(std::vector<IntegerVariableID> vars, const IntegerVariableID & value_of_interest, const IntegerVariableID & how_many) :
    _vars(move(vars)),
    _value_of_interest(value_of_interest),
    _how_many(how_many)
{
}

auto Count::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Count>(_vars, _value_of_interest, _how_many);
}

auto Count::install(Propagators & propagators, State &, ProofModel * const optional_model) && -> void
{
    Triggers triggers;
    triggers.on_change.insert(triggers.on_change.end(), _vars.begin(), _vars.end());
    triggers.on_change.emplace_back(_value_of_interest);
    triggers.on_bounds.emplace_back(_how_many);

    vector<tuple<ProofFlag, ProofFlag, ProofFlag>> flags;
    if (optional_model) {
        for (auto & var : _vars) {
            auto flag = optional_model->create_proof_flag("count");
            auto var_minus_val_gt_0 = optional_model->create_proof_flag("countg");
            auto var_minus_val_lt_0 = optional_model->create_proof_flag("countl");
            flags.emplace_back(flag, var_minus_val_gt_0, var_minus_val_lt_0);

            // var_minus_val_gt_0 -> var - val > 0
            optional_model->add_constraint("Count", "var bigger",
                    WeightedPseudoBooleanSum{} + 1_i * var + -1_i * _value_of_interest >= 1_i, HalfReifyOnConjunctionOf{{var_minus_val_gt_0}});

            // ! var_minus_val_gt_0 -> var - val <= 0
            optional_model->add_constraint("Count", "var not bigger",
                    WeightedPseudoBooleanSum{} + 1_i * var + -1_i * _value_of_interest <= 0_i, HalfReifyOnConjunctionOf{{! var_minus_val_gt_0}});

            // var_minus_val_lt_0 -> var - val <= -1
            optional_model->add_constraint("Count", "var smaller", WeightedPseudoBooleanSum{} + 1_i * var + -1_i * _value_of_interest <= -1_i, HalfReifyOnConjunctionOf{{var_minus_val_lt_0}});

            // ! var_minus_val_lt_0 -> var - val > -1
            optional_model->add_constraint("Count", "var not smaller", WeightedPseudoBooleanSum{} + 1_i * var + -1_i * _value_of_interest >= 0_i, HalfReifyOnConjunctionOf{{! var_minus_val_lt_0}});

            // flag => ! countg /\ ! countl
            optional_model->add_constraint("Count", "var equal", WeightedPseudoBooleanSum{} + 1_i * ! var_minus_val_gt_0 + 1_i * ! var_minus_val_lt_0 >= 2_i, HalfReifyOnConjunctionOf{{flag}});

            // ! flag => countg \/ countl
            optional_model->add_constraint("Count", "var not equal", WeightedPseudoBooleanSum{} + 1_i * var_minus_val_gt_0 + 1_i * var_minus_val_lt_0 >= 1_i, HalfReifyOnConjunctionOf{{! flag}});
        }

        // sum flag == how_many
        WeightedPseudoBooleanSum how_many_sum;
        for (auto & [flag, _1, _2] : flags)
            how_many_sum += 1_i * flag;
        how_many_sum += -1_i * _how_many;

        optional_model->add_constraint("Count", "sum of flags", how_many_sum == 0_i);
    }

    propagators.install(
        [vars = _vars, value_of_interest = _value_of_interest, how_many = _how_many, flags = flags](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // check support for how many by seeing how many array values
            // intersect with a potential value of interest
            int how_many_definitely_do_not = 0;
            auto viable_places = 0_i;
            vector<pair<size_t, IntegerVariableID>> not_seen_any_vars;
            for (const auto & [idx, var] : enumerate(vars)) {
                bool seen_any = false;
                for (const auto & voi : state.each_value(value_of_interest)) {
                    if (state.in_domain(var, voi)) {
                        seen_any = true;
                        break;
                    }
                }

                if (! seen_any) {
                    ++how_many_definitely_do_not;
                    not_seen_any_vars.emplace_back(idx, var);
                }
                else
                    ++viable_places;
            }

            // can't have more that this many occurrences of the value of interest
            auto how_many_is_less_than = Integer(vars.size() - how_many_definitely_do_not) + 1_i;
            auto justf = [&vars, not_seen_any_vars = move(not_seen_any_vars), value_of_interest, &flags,
                             values_of_interest_values = state.copy_of_values(value_of_interest)](ProofLogger & logger, const ExpandedReason & reason) -> void {
                for (const auto & [idx, var] : not_seen_any_vars) {
                    for (const auto & val : values_of_interest_values.each()) {
                        logger.emit_rup_proof_line_under_reason(reason,
                            WeightedPseudoBooleanSum{} + 1_i * (value_of_interest != val) + 1_i * (! get<0>(flags[idx])) >= 1_i, ProofLevel::Temporary);
                    }
                    logger.emit_rup_proof_line_under_reason(reason,
                        WeightedPseudoBooleanSum{} + 1_i * (! get<0>(flags[idx])) >= 1_i, ProofLevel::Temporary);
                }
            };
            inference.infer(logger, how_many < how_many_is_less_than,
                JustifyExplicitly{justf},
                AllVariablesExactValues{});

            // must have at least this many occurrences of the value of interest
            int how_many_must = 0;
            auto voi = state.optional_single_value(value_of_interest);
            if (voi) {
                for (auto & v : vars)
                    if (state.optional_single_value(v) == voi)
                        ++how_many_must;
            }
            inference.infer(logger, how_many >= Integer(how_many_must), JustifyUsingRUP{}, AllVariablesExactValues{});

            // is each value of interest supported? also track how_many bounds supports
            // whilst we're here
            optional<Integer> lowest_how_many_must, highest_how_many_might;
            for (const auto & voi : state.each_value(value_of_interest)) {
                Integer how_many_must = 0_i, how_many_might = 0_i;
                vector<pair<size_t, IntegerVariableID>> non_matching_vars;
                for (const auto & [idx, var] : enumerate(vars)) {
                    if (auto sv = state.optional_single_value(var)) {
                        if (*sv == voi) {
                            ++how_many_must;
                            ++how_many_might;
                        }
                        else
                            non_matching_vars.emplace_back(idx, var);
                    }
                    else if (state.in_domain(var, voi))
                        ++how_many_might;
                    else
                        non_matching_vars.emplace_back(idx, var);
                }

                if (how_many_might < state.lower_bound(how_many)) {
                    auto justf = [non_matching_vars = move(non_matching_vars), value_of_interest, voi, &flags](ProofLogger & logger, const ExpandedReason & reason) -> void {
                        for (const auto & [idx, var] : non_matching_vars) {
                            // need to help the checker see that the equality flag must be zero
                            logger.emit_rup_proof_line(
                                WeightedPseudoBooleanSum{} + 1_i * (value_of_interest != voi) + 1_i * (var != voi) + 1_i * (get<0>(flags[idx])) >= 1_i, ProofLevel::Temporary);
                            logger.emit_rup_proof_line_under_reason(reason,
                                WeightedPseudoBooleanSum{} + 1_i * (value_of_interest != voi) + 1_i * (! get<0>(flags[idx])) >= 1_i, ProofLevel::Temporary);
                        }
                    };
                    inference.infer(logger, value_of_interest != voi, JustifyExplicitly{justf}, AllVariablesExactValues{});
                }
                else if (how_many_must > state.upper_bound(how_many)) {
                    // unlike above, we don't need to help, because the equality flag will propagate
                    // from the fixed assignment
                    inference.infer(logger, value_of_interest != voi, JustifyUsingRUP{}, AllVariablesExactValues{});
                }
                else {
                    if ((! lowest_how_many_must) || (how_many_must < *lowest_how_many_must))
                        lowest_how_many_must = how_many_must;
                    if ((! highest_how_many_might) || (how_many_might > *highest_how_many_might))
                        highest_how_many_might = how_many_might;
                }
            }

            // what are the supports on possible values we've seen?
            if (lowest_how_many_must) {
                auto just = JustifyExplicitly{
                    [value_of_interest_values = state.copy_of_values(value_of_interest), value_of_interest, how_many, lowest_how_many_must = *lowest_how_many_must](
                        ProofLogger & logger, const ExpandedReason & reason) -> void {
                        for (const auto & voi : value_of_interest_values.each()) {
                            logger.emit_rup_proof_line_under_reason(reason,
                                WeightedPseudoBooleanSum{} + 1_i * (value_of_interest != voi) + 1_i * (how_many >= lowest_how_many_must) >= 1_i,
                                ProofLevel::Temporary);
                        }
                    }};
                inference.infer(logger, how_many >= *lowest_how_many_must, just, AllVariablesExactValues{});
            }

            if (highest_how_many_might) {
                auto just = JustifyExplicitly{
                    [&](ProofLogger & logger, const ExpandedReason & reason) -> void {
                        state.for_each_value_while_immutable(value_of_interest, [&](Integer voi) -> bool {
                            for (const auto & [idx, var] : enumerate(vars)) {
                                if (! state.in_domain(var, voi)) {
                                    logger.emit_rup_proof_line_under_reason(reason,
                                        WeightedPseudoBooleanSum{} + 1_i * (value_of_interest != voi) + 1_i * (! get<0>(flags[idx])) >= 1_i,
                                        ProofLevel::Temporary);
                                    logger.emit_rup_proof_line_under_reason(reason,
                                        WeightedPseudoBooleanSum{} + 1_i * (value_of_interest != voi) + 1_i * (var != voi) >= 1_i,
                                        ProofLevel::Temporary);
                                }
                            }

                            logger.emit_rup_proof_line_under_reason(reason,
                                WeightedPseudoBooleanSum{} + 1_i * (value_of_interest != voi) + 1_i * (how_many < *highest_how_many_might + 1_i) >= 1_i,
                                ProofLevel::Temporary);
                            return true;
                        });
                    }};
                inference.infer(logger, how_many < *highest_how_many_might + 1_i, just, AllVariablesExactValues{});
            }

            return PropagatorState::Enable;
        },
        {_vars, _value_of_interest, _how_many}, triggers, "count");
}
