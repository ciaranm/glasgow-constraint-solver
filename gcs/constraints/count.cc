#include <gcs/constraints/count.hh>
#include <gcs/innards/inference_tracker.hh>
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

auto Count::install(Propagators & propagators, State & initial_state) && -> void
{
    Triggers triggers;
    triggers.on_change.insert(triggers.on_change.end(), _vars.begin(), _vars.end());
    triggers.on_change.emplace_back(_value_of_interest);
    triggers.on_bounds.emplace_back(_how_many);

    vector<tuple<ProofFlag, ProofFlag, ProofFlag>> flags;
    if (propagators.want_definitions()) {
        for (auto & var : _vars) {
            auto flag = propagators.create_proof_flag("count");
            auto var_minus_val_gt_0 = propagators.create_proof_flag("countg");
            auto var_minus_val_lt_0 = propagators.create_proof_flag("countl");
            flags.emplace_back(flag, var_minus_val_gt_0, var_minus_val_lt_0);

            // var_minus_val_gt_0 -> var - val >= 1
            propagators.define(initial_state, WeightedPseudoBooleanSum{} + 1_i * var + -1_i * _value_of_interest >= 1_i, HalfReifyOnConjunctionOf{{var_minus_val_gt_0}});

            // ! var_minus_val_gt_0 -> var - val < 1
            propagators.define(initial_state, WeightedPseudoBooleanSum{} + 1_i * var + -1_i * _value_of_interest <= 0_i, HalfReifyOnConjunctionOf{{! var_minus_val_gt_0}});

            // var_minus_val_lt_0 -> var - val <= -1
            propagators.define(initial_state, WeightedPseudoBooleanSum{} + 1_i * var + -1_i * _value_of_interest <= -1_i, HalfReifyOnConjunctionOf{{var_minus_val_lt_0}});

            // ! var_minus_val_lt_0 -> var - val > -1
            propagators.define(initial_state, WeightedPseudoBooleanSum{} + 1_i * var + -1_i * _value_of_interest >= 0_i, HalfReifyOnConjunctionOf{{! var_minus_val_lt_0}});

            // flag => ! countg /\ ! countl
            propagators.define(initial_state, WeightedPseudoBooleanSum{} + 1_i * ! var_minus_val_gt_0 + 1_i * ! var_minus_val_lt_0 >= 2_i, HalfReifyOnConjunctionOf{{flag}});

            // ! flag => countg \/ countl
            propagators.define(initial_state, WeightedPseudoBooleanSum{} + 1_i * var_minus_val_gt_0 + 1_i * var_minus_val_lt_0 >= 1_i, HalfReifyOnConjunctionOf{{! flag}});
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

        propagators.define(initial_state, forward >= forward_g);
        propagators.define(initial_state, reverse >= reverse_g);
    }

    propagators.install_tracking(
        [vars = _vars, value_of_interest = _value_of_interest, how_many = _how_many, flags = flags](
            State & state, InferenceTracker & inference) -> PropagatorState {
            // check support for how many by seeing how many array values
            // intersect with a potential value of interest
            int how_many_definitely_do_not = 0;
            auto viable_places = 0_i;
            for (auto & var : vars) {
                bool seen_any = false;
                state.for_each_value_while_immutable(value_of_interest, [&](const Integer & voi) {
                    if (state.in_domain(var, voi))
                        seen_any = true;
                    return ! seen_any;
                });

                if (! seen_any)
                    ++how_many_definitely_do_not;
                else
                    ++viable_places;
            }

            // can't have more that this many occurrences of the value of interest
            auto how_many_is_less_than = Integer(vars.size() - how_many_definitely_do_not) + 1_i;
            inference.infer(how_many < how_many_is_less_than, JustifyExplicitly{[&](Proof & proof) -> void {
                for (const auto & [idx, var] : enumerate(vars)) {
                    bool seen_any = false;
                    state.for_each_value_while_immutable(var, [&](const Integer & val) -> bool {
                        if (state.in_domain(value_of_interest, val))
                            seen_any = true;
                        return ! seen_any;
                    });

                    if (! seen_any)
                        proof.emit_rup_proof_line_under_trail(state,
                            WeightedPseudoBooleanSum{} + 1_i * (! get<0>(flags[idx])) >= 1_i, ProofLevel::Temporary);
                }
            }});

            // must have at least this many occurrences of the value of interest
            int how_many_must = 0;
            auto voi = state.optional_single_value(value_of_interest);
            if (voi) {
                for (auto & v : vars)
                    if (state.optional_single_value(v) == voi)
                        ++how_many_must;
            }
            inference.infer(how_many >= Integer(how_many_must), JustifyUsingRUP{});

            // is each value of interest supported? also track how_many bounds supports
            // whilst we're here
            optional<Integer> lowest_how_many_must, highest_how_many_might;
            state.for_each_value_while(value_of_interest, [&](Integer voi) {
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
                    inference.infer(value_of_interest != voi, JustifyExplicitly{[&](Proof & proof) -> void {
                        for (const auto & [idx, var] : enumerate(vars)) {
                            if (! state.in_domain(var, voi)) {
                                // need to help the checker see that the equality flag must be zero
                                proof.emit_rup_proof_line(
                                    WeightedPseudoBooleanSum{} + 1_i * (value_of_interest != voi) + 1_i * (var != voi) + 1_i * (get<0>(flags[idx])) >= 1_i, ProofLevel::Temporary);
                                proof.emit_rup_proof_line_under_trail(state,
                                    WeightedPseudoBooleanSum{} + 1_i * (value_of_interest != voi) + 1_i * (! get<0>(flags[idx])) >= 1_i, ProofLevel::Temporary);
                            }
                        }
                    }});
                }
                else if (how_many_must > state.upper_bound(how_many)) {
                    // unlike above, we don't need to help, because the equality flag will propagate
                    // from the fixed assignment
                    inference.infer(value_of_interest != voi, JustifyUsingRUP{});
                }
                else {
                    if ((! lowest_how_many_must) || (how_many_must < *lowest_how_many_must))
                        lowest_how_many_must = how_many_must;
                    if ((! highest_how_many_might) || (how_many_might > *highest_how_many_might))
                        highest_how_many_might = how_many_might;
                }

                return true;
            });

            // what are the supports on possible values we've seen?
            if (lowest_how_many_must) {
                inference.infer(how_many >= *lowest_how_many_must, JustifyExplicitly{[&](Proof & proof) -> void {
                    state.for_each_value_while_immutable(value_of_interest, [&](Integer voi) -> bool {
                        proof.emit_rup_proof_line_under_trail(state,
                            WeightedPseudoBooleanSum{} + 1_i * (value_of_interest != voi) + 1_i * (how_many >= *lowest_how_many_must) >= 1_i,
                            ProofLevel::Temporary);
                        return true;
                    });
                }});
            }

            if (highest_how_many_might) {
                inference.infer(how_many < *highest_how_many_might + 1_i, JustifyExplicitly{[&](Proof & proof) -> void {
                    state.for_each_value_while_immutable(value_of_interest, [&](Integer voi) -> bool {
                        for (const auto & [idx, var] : enumerate(vars)) {
                            if (! state.in_domain(var, voi)) {
                                proof.emit_rup_proof_line_under_trail(state,
                                    WeightedPseudoBooleanSum{} + 1_i * (value_of_interest != voi) + 1_i * (! get<0>(flags[idx])) >= 1_i,
                                    ProofLevel::Temporary);
                                proof.emit_rup_proof_line_under_trail(state,
                                    WeightedPseudoBooleanSum{} + 1_i * (value_of_interest != voi) + 1_i * (var != voi) >= 1_i,
                                    ProofLevel::Temporary);
                            }
                        }

                        proof.emit_rup_proof_line_under_trail(state,
                            WeightedPseudoBooleanSum{} + 1_i * (value_of_interest != voi) + 1_i * (how_many < *highest_how_many_might + 1_i) >= 1_i,
                            ProofLevel::Temporary);
                        return true;
                    });
                }});
            }

            return PropagatorState::Enable;
        },
        triggers, "count");
}

auto Count::describe_for_proof() -> std::string
{
    return "count";
}
