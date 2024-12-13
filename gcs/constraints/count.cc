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

            // var_minus_val_gt_0 -> var - val >= 1
            optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * var + -1_i * _value_of_interest >= 1_i, HalfReifyOnConjunctionOf{{var_minus_val_gt_0}});

            // ! var_minus_val_gt_0 -> var - val < 1
            optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * var + -1_i * _value_of_interest <= 0_i, HalfReifyOnConjunctionOf{{! var_minus_val_gt_0}});

            // var_minus_val_lt_0 -> var - val <= -1
            optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * var + -1_i * _value_of_interest <= -1_i, HalfReifyOnConjunctionOf{{var_minus_val_lt_0}});

            // ! var_minus_val_lt_0 -> var - val > -1
            optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * var + -1_i * _value_of_interest >= 0_i, HalfReifyOnConjunctionOf{{! var_minus_val_lt_0}});

            // flag => ! countg /\ ! countl
            optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * ! var_minus_val_gt_0 + 1_i * ! var_minus_val_lt_0 >= 2_i, HalfReifyOnConjunctionOf{{flag}});

            // ! flag => countg \/ countl
            optional_model->add_constraint(WeightedPseudoBooleanSum{} + 1_i * var_minus_val_gt_0 + 1_i * var_minus_val_lt_0 >= 1_i, HalfReifyOnConjunctionOf{{! flag}});
        }

        // sum flag == how_many
        WeightedPseudoBooleanSum forward, reverse;
        for (auto & [flag, _1, _2] : flags) {
            forward += 1_i * flag;
            reverse += -1_i * flag;
        }
        forward += -1_i * _how_many;
        reverse += 1_i * _how_many;
        Integer forward_g = 0_i, reverse_g = 0_i;

        optional_model->add_constraint(forward >= forward_g);
        optional_model->add_constraint(reverse >= reverse_g);
    }

    vector<IntegerVariableID> all_vars = _vars;
    all_vars.push_back(_value_of_interest);
    all_vars.push_back(_how_many);

    propagators.install(
        [vars = _vars, value_of_interest = _value_of_interest, how_many = _how_many, flags = flags, all_vars = move(all_vars)](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // check support for how many by seeing how many array values
            // intersect with a potential value of interest
            int how_many_definitely_do_not = 0;
            auto viable_places = 0_i;
            for (auto & var : vars) {
                bool seen_any = false;
                for (const auto & voi : state.each_value_immutable(value_of_interest)) {
                    if (state.in_domain(var, voi)) {
                        seen_any = true;
                        break;
                    }
                }

                if (! seen_any)
                    ++how_many_definitely_do_not;
                else
                    ++viable_places;
            }

            // can't have more that this many occurrences of the value of interest
            auto how_many_is_less_than = Integer(vars.size() - how_many_definitely_do_not) + 1_i;
            auto justf = [&](const Reason & reason) -> void {
                for (const auto & [idx, var] : enumerate(vars)) {
                    bool seen_any = false;
                    state.for_each_value_while_immutable(var, [&](const Integer & val) -> bool {
                        if (state.in_domain(value_of_interest, val))
                            seen_any = true;
                        return ! seen_any;
                    });

                    if (! seen_any)
                        logger->emit_rup_proof_line_under_reason(reason,
                            WeightedPseudoBooleanSum{} + 1_i * (! get<0>(flags[idx])) >= 1_i, ProofLevel::Temporary);
                }
            };
            inference.infer(logger, how_many < how_many_is_less_than, JustifyExplicitly{justf}, generic_reason(state, all_vars));

            // must have at least this many occurrences of the value of interest
            int how_many_must = 0;
            auto voi = state.optional_single_value(value_of_interest);
            if (voi) {
                for (auto & v : vars)
                    if (state.optional_single_value(v) == voi)
                        ++how_many_must;
            }
            inference.infer(logger, how_many >= Integer(how_many_must), JustifyUsingRUP{}, generic_reason(state, all_vars));

            // is each value of interest supported? also track how_many bounds supports
            // whilst we're here
            optional<Integer> lowest_how_many_must, highest_how_many_might;
            for (const auto & voi : state.each_value_mutable(value_of_interest)) {
                Integer how_many_must = 0_i, how_many_might = 0_i;
                for (const auto & var : vars) {
                    if (auto sv = state.optional_single_value(var)) {
                        if (*sv == voi) {
                            ++how_many_must;
                            ++how_many_might;
                        }
                    }
                    else if (state.in_domain(var, voi))
                        ++how_many_might;
                }

                if (how_many_might < state.lower_bound(how_many)) {
                    auto justf = [&](const Reason & reason) -> void {
                        for (const auto & [idx, var] : enumerate(vars)) {
                            if (! state.in_domain(var, voi)) {
                                // need to help the checker see that the equality flag must be zero
                                logger->emit_rup_proof_line(
                                    WeightedPseudoBooleanSum{} + 1_i * (value_of_interest != voi) + 1_i * (var != voi) + 1_i * (get<0>(flags[idx])) >= 1_i, ProofLevel::Temporary);
                                logger->emit_rup_proof_line_under_reason(reason,
                                    WeightedPseudoBooleanSum{} + 1_i * (value_of_interest != voi) + 1_i * (! get<0>(flags[idx])) >= 1_i, ProofLevel::Temporary);
                            }
                        }
                    };
                    inference.infer(logger, value_of_interest != voi, JustifyExplicitly{justf}, generic_reason(state, all_vars));
                }
                else if (how_many_must > state.upper_bound(how_many)) {
                    // unlike above, we don't need to help, because the equality flag will propagate
                    // from the fixed assignment
                    inference.infer(logger, value_of_interest != voi, JustifyUsingRUP{}, generic_reason(state, all_vars));
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
                    [&](const Reason & reason) -> void {
                        state.for_each_value_while_immutable(value_of_interest, [&](Integer voi) -> bool {
                            logger->emit_rup_proof_line_under_reason(reason,
                                WeightedPseudoBooleanSum{} + 1_i * (value_of_interest != voi) + 1_i * (how_many >= *lowest_how_many_must) >= 1_i,
                                ProofLevel::Temporary);
                            return true;
                        });
                    }};
                inference.infer(logger, how_many >= *lowest_how_many_must, just, generic_reason(state, all_vars));
            }

            if (highest_how_many_might) {
                auto just = JustifyExplicitly{
                    [&](const Reason & reason) -> void {
                        state.for_each_value_while_immutable(value_of_interest, [&](Integer voi) -> bool {
                            for (const auto & [idx, var] : enumerate(vars)) {
                                if (! state.in_domain(var, voi)) {
                                    logger->emit_rup_proof_line_under_reason(reason,
                                        WeightedPseudoBooleanSum{} + 1_i * (value_of_interest != voi) + 1_i * (! get<0>(flags[idx])) >= 1_i,
                                        ProofLevel::Temporary);
                                    logger->emit_rup_proof_line_under_reason(reason,
                                        WeightedPseudoBooleanSum{} + 1_i * (value_of_interest != voi) + 1_i * (var != voi) >= 1_i,
                                        ProofLevel::Temporary);
                                }
                            }

                            logger->emit_rup_proof_line_under_reason(reason,
                                WeightedPseudoBooleanSum{} + 1_i * (value_of_interest != voi) + 1_i * (how_many < *highest_how_many_might + 1_i) >= 1_i,
                                ProofLevel::Temporary);
                            return true;
                        });
                    }};
                inference.infer(logger, how_many < *highest_how_many_might + 1_i, just, generic_reason(state, all_vars));
            }

            return PropagatorState::Enable;
        },
        triggers, "count");
}
