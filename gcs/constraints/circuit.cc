#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/circuit.hh>
#include <gcs/exception.hh>
#include <gcs/innards/propagators.hh>

#include <util/enumerate.hh>

#include <map>
#include <sstream>
#include <utility>
#include <iostream>

using namespace gcs;
using namespace gcs::innards;

using std::cmp_less;
using std::cmp_not_equal;
using std::make_pair;
using std::map;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::stringstream;
using std::to_string;
using std::unique_ptr;
using std::vector;

using ProofLine2DMap = map<pair<Integer, Integer>, ProofLine>;

Circuit::Circuit(vector<IntegerVariableID> v, const bool p, const bool g) :
    _succ(move(v)),
    _propagate_using_check_only(p),
    _gac_all_different(g)
{
}

namespace
{
    auto propagate_non_gac_alldifferent(const vector<IntegerVariableID> & succ, State & state) -> Inference
    {
        auto result = Inference::NoChange;
        {
            vector<bool> being_done(succ.size(), false);
            vector<pair<IntegerVariableID, Integer>> to_propagate;
            for (auto [idx, s] : enumerate(succ))
                if (auto val = state.optional_single_value(s)) {
                    to_propagate.emplace_back(s, *val);
                    being_done[idx] = true;
                }
            while (! to_propagate.empty()) {
                auto [var, val] = to_propagate.back();
                to_propagate.pop_back();
                for (auto [other_idx, other] : enumerate(succ))
                    if (other != var) {
                        increase_inference_to(result, state.infer_not_equal(other, val, JustifyUsingRUP{}));
                        if (result == Inference::Contradiction) return Inference::Contradiction;
                        if (! being_done[other_idx])
                            if (auto other_val = state.optional_single_value(other)) {
                                being_done[other_idx] = true;
                                to_propagate.emplace_back(other, *other_val);
                            }
                    }
            }
        }
        return result;

    }

    // Most basic propagator: just check if there are any cycles that tour less than all of the variables
    auto propagate_circuit_using_check(const vector<IntegerVariableID> & succ,
        const ProofLine2DMap & lines_for_setting_pos, State & state) -> Inference
    {
        // propagate all-different first, to avoid infinte loops
        auto result = propagate_non_gac_alldifferent(succ, state);
        if (result == Inference::Contradiction) return Inference::Contradiction;

        vector<bool> checked(succ.size(), false);
        for (const auto & [uidx, var] : enumerate(succ)) {
            // Convert the unsigned idx to signed idx to avoid warning when making Integer
            auto idx = static_cast<long long>(uidx);

            if (checked[idx]) continue;

            checked[idx] = true;
            auto current_val = state.optional_single_value(var);
            if (current_val == nullopt) continue;
            if (current_val->raw_value < 0)
                throw UnimplementedException("Successor encoding for circuit can't have negative values");

            bool finished_cycle = true;
            unsigned long cycle_length = 1;

            stringstream proof_step;
            bool need_justification = false;

            if (state.maybe_proof()) {
                proof_step << "p ";
                proof_step << lines_for_setting_pos.at(make_pair(current_val.value(), Integer(idx))) + 1 << " ";
            }

            while (cmp_not_equal(current_val->raw_value, idx)) {
                auto last_val = current_val;
                auto next_var = succ[last_val->raw_value];
                current_val = state.optional_single_value(next_var);

                if (current_val == nullopt) {
                    finished_cycle = false;
                    break;
                }

                checked[current_val->raw_value] = true;

                if (state.maybe_proof()) {
                    proof_step << lines_for_setting_pos.at(make_pair(current_val.value(), last_val.value())) + 1
                               << " + ";
                    need_justification = true;
                }

                cycle_length++;
            }

            if (finished_cycle && cycle_length < succ.size()) {
                if (need_justification)
                    return state.infer(FalseLiteral{}, JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & to_delete) -> void {
                        to_delete.push_back(proof.emit_proof_line(proof_step.str()));
                    }});
                return Inference::Contradiction;
            }
        }

        return result;
    }

    // Slightly more complex propagator: prevent small cycles by finding chains and removing the head from the domain
    // of the tail.
    auto propagate_circuit_using_prevent(const vector<IntegerVariableID> & succ,
                                         const ProofLine2DMap & lines_for_setting_pos,
                                         State & state,
                                         const IntegerVariableID & trigger_var,
                                         const long & trigger_idx,
                                         const ConstraintStateHandle & chain_start_idx,
                                         const ConstraintStateHandle & chain_end_idx,
                                         const ConstraintStateHandle & chain_length_idx,
                                         bool& should_disable) -> Inference
    {

        // propagate all-different first, to avoid infinite loops
        // Have to use check first
        auto result = propagate_non_gac_alldifferent(succ, state);
        if (result == Inference::Contradiction) return Inference::Contradiction;

        auto& chain_start = any_cast<vector<long long> &>(state.get_constraint_state(chain_start_idx));
        auto& chain_end = any_cast<vector<long long> &>(state.get_constraint_state(chain_end_idx));
        auto& chain_length = any_cast<vector<long long> &>(state.get_constraint_state(chain_length_idx));
        auto n = succ.size();

        auto current_idx = trigger_idx;
        auto var = trigger_var;
        auto value = state.optional_single_value(var);
        if(value == nullopt)
            return result;
        auto start = chain_start[current_idx];
        auto next_idx = value->raw_value;
        auto end = chain_end[next_idx];

        if(cmp_not_equal(chain_length[start],n) && next_idx == start) {
            return Inference::Contradiction;
        } else {
            chain_length[start] += chain_length[next_idx];
            chain_start[end] = start;
            chain_end[start] = end;

            if(cmp_less(chain_length[start], succ.size())) {
                increase_inference_to(result, state.infer(succ[end] != Integer{start}, NoJustificationNeeded{}));
            } else {
                increase_inference_to(result, state.infer(succ[end] == Integer{start}, NoJustificationNeeded{}));
                return result;
            }

            if (result == Inference::Contradiction) {
                return Inference::Contradiction;
            }

            if(state.optional_single_value(succ[end])) {
                should_disable = true;
            }
        }


        return result;
    }
}

auto Circuit::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Circuit>(_succ, _propagate_using_check_only, _gac_all_different);
}

auto Circuit::install(Propagators & propagators, State & initial_state) && -> void
{
    // Can't have negative values
    for (const auto & s : _succ)
        propagators.trim_lower_bound(initial_state, s, 0_i, "Circuit");

    // Can't have too-large values
    for (const auto & s : _succ)
        propagators.trim_upper_bound(initial_state, s, Integer(_succ.size() - 1), "Circuit");

    if (_gac_all_different) {
        // First define an all different constraint
        AllDifferent all_diff{_succ};
        move(all_diff).install(propagators, initial_state);
    }
    else if (propagators.want_definitions()) {
        // Still need to define all-different
        for (unsigned i = 0; i < _succ.size(); ++i)
            for (unsigned j = i + 1; j < _succ.size(); ++j) {
                auto selector = propagators.create_proof_flag("circuit_notequals");

                auto cv1 = Linear{{1_i, _succ[i]}, {-1_i, _succ[j]}};
                propagators.define_linear_le(initial_state, cv1, -1_i, selector);

                auto cv2 = Linear{{-1_i, _succ[i]}, {1_i, _succ[j]}};
                propagators.define_linear_le(initial_state, cv2, -1_i, ! selector);
            }
    }

    ProofLine2DMap lines_for_setting_pos{};
    if (propagators.want_definitions()) {
        // Define encoding to eliminate sub-cycles
        vector<PseudoBooleanTerm> position;
        auto n_minus_1 = ConstantIntegerVariableID{Integer{static_cast<long long>(_succ.size() - 1)}};

        // Need extra proof variable: pos[i] = j means "the ith node visited in the circuit is the jth var"
        // WLOG start at node 0, so pos[0] = 0
        position.emplace_back(0_c);
        // Hence we can only have succ[0] = 0 (self cycle) if there is only one node i.e. n - 1 = 0
        auto cv = WeightedPseudoBooleanTerms{{1_i, position[0]}, {-1_i, n_minus_1}};
        auto proof_line = propagators.define_pseudoboolean_eq(initial_state, move(cv), 0_i, _succ[0] == 0_i);
        lines_for_setting_pos.insert({{Integer{0_i}, Integer{0_i}}, proof_line.value()});

        for (unsigned int idx = 1; idx < _succ.size(); ++idx) {
            position.emplace_back(propagators.create_proof_only_integer_variable(0_i, Integer(_succ.size() - 1),
                "pos" + to_string(idx), IntegerVariableProofRepresentation::Bits));
        }

        for (unsigned int idx = 1; idx < _succ.size(); ++idx) {
            // (succ[0] = i) -> pos[i] = 1
            auto cv1 = WeightedPseudoBooleanTerms{{1_i, position[idx]}, {-1_i, 1_c}};
            proof_line = propagators.define_pseudoboolean_eq(initial_state, move(cv1), 0_i, _succ[0] == Integer{idx});
            lines_for_setting_pos.insert({{Integer{idx}, Integer{0_i}}, proof_line.value()});

            // (succ[i] = 0) -> pos[i] = n-1
            auto cv2 = WeightedPseudoBooleanTerms{{1_i, position[idx]}, {-1_i, n_minus_1}};

            proof_line = propagators.define_pseudoboolean_eq(initial_state, move(cv2), 0_i, _succ[idx] == 0_i);
            lines_for_setting_pos.insert({{Integer{0_i}, Integer{idx}}, proof_line.value()});

            // (succ[i] = j) -> pos[j] = pos[i] + 1
            for (unsigned int jdx = 1; jdx < _succ.size(); ++jdx) {
                // if (idx == jdx) continue;
                auto cv3 = WeightedPseudoBooleanTerms{{1_i, position[jdx]}, {-1_i, position[idx]}, {-1_i, 1_c}};

                proof_line = propagators.define_pseudoboolean_eq(initial_state, move(cv3), 0_i, _succ[idx] == Integer{jdx});
                lines_for_setting_pos.insert({{Integer{jdx}, Integer{idx}}, proof_line.value()});
            }
        }
    }





    if(_propagate_using_check_only) {
        // For basic "check" algorithm, only trigger when variable gains a unique value
        // Same applies for prevent, I think
        Triggers triggers;
        triggers.on_instantiated = {_succ.begin(), _succ.end()};
        propagators.install(
                [succ = _succ,lines_for_setting_pos = lines_for_setting_pos](State & state) -> pair<Inference, PropagatorState> {
                    return pair{
                            propagate_circuit_using_check(succ, lines_for_setting_pos, state),
                            PropagatorState::Enable};
                },
                triggers,
                "circuit");
    } else {
        // Constraint states for prevent algorithm
        vector<long long> chain_start;
        vector<long long> chain_end;
        vector<long long> chain_length;

        for(unsigned int idx = 0; idx < _succ.size(); idx++) {
            chain_start.emplace_back(idx);
            chain_end.emplace_back(idx);
            chain_length.emplace_back(1);
        }
        auto chain_start_idx = initial_state.add_constraint_state(chain_start);
        auto chain_end_idx = initial_state.add_constraint_state(chain_end);
        auto chain_length_idx = initial_state.add_constraint_state(chain_length);

        for(unsigned int idx = 0; idx < _succ.size(); idx++) {
            Triggers triggers;
            triggers.on_instantiated = {_succ[idx]};
            propagators.install(
                    [succ = _succ, idx=idx, lines_for_setting_pos = lines_for_setting_pos, start=chain_start_idx,
                     end=chain_end_idx, length=chain_length_idx]
                    (State & state) -> pair<Inference, PropagatorState> {
                        bool should_disable = false;
                        auto result = propagate_circuit_using_prevent(
                                succ, lines_for_setting_pos, state, succ[idx], idx, start, end, length, should_disable);
                        return pair{
                                result,
                                should_disable ? PropagatorState::DisableUntilBacktrack : PropagatorState::Enable};
                    },
                    triggers,
                    "circuit");
        }

    }



    // Infer succ[i] != i at top of search
    if (_succ.size() > 1) {
        propagators.install([succ = _succ](State & state) -> pair<Inference, PropagatorState> {
            auto result = Inference::NoChange;
            for (auto [idx, s] : enumerate(succ)) {
                increase_inference_to(result, state.infer_not_equal(s, Integer(idx), JustifyUsingRUP{}));
                if (result == Inference::Contradiction)
                    break;
            }
            return pair{result, PropagatorState::DisableUntilBacktrack};
        },
            Triggers{}, "circuit init");
    }
}

auto Circuit::describe_for_proof() -> std::string
{
    return "circuit (all different + no sub-cycles)";
}
