#include <gcs/constraints/circuit.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/constraints/all_different.hh>

#include <util/enumerate.hh>

#include <utility>
#include <map>
#include <iostream>
using namespace gcs;
using namespace gcs::innards;

using std::vector;
using std::move;
using std::optional;
using std::nullopt;
using std::to_string;
using std::pair;
using std::unique_ptr;
using std::stringstream;
using std::map;
using std::make_pair;

using ProofLine2DMap = map<pair<Integer, Integer>, ProofLine>;

Circuit::Circuit(const vector<IntegerVariableID> & v, const bool p) :
    _succ(v),
    _propagate_using_check_only(p)
{
}

namespace {

    // Most basic propagator: just check if there are any cycles that tour less than all of the variables
    auto propagate_circuit_using_check(vector<IntegerVariableID> succ, ProofLine2DMap lines_for_setting_pos, State& state) -> Inference {
        vector<bool> checked(succ.size(), false);
        for(const auto & [idx, var]: enumerate(succ)) {
            if(checked[idx]) continue;

            checked[idx] = true;
            auto current_val = state.optional_single_value(var);
            if(current_val == nullopt) continue;
            if(current_val->raw_value < 0) return Inference::Contradiction; // shouldn't happen

            bool finished_cycle = true;
            unsigned long cycle_length = 1;

            stringstream proof_step;
            proof_step << "p ";
            bool need_justification = false;

            proof_step << lines_for_setting_pos.at(make_pair(current_val.value(), Integer(idx))) + 1 << " ";

            while(current_val->raw_value != idx) {
                auto last_val = current_val;
                auto next_var = succ[last_val->raw_value];
                current_val = state.optional_single_value(next_var);

                if(current_val == nullopt) {
                    finished_cycle = false;
                    break;
                }

                checked[current_val->raw_value] = true;

                proof_step << lines_for_setting_pos.at(make_pair(current_val.value(), last_val.value())) + 1 << " + ";
                need_justification = true;

                cycle_length++;
            }

            if(finished_cycle && cycle_length < succ.size()) {
                if(need_justification)
                    return state.infer(FalseLiteral{}, JustifyExplicitly{[&](Proof & proof, vector<ProofLine> &) -> void {
                        proof.emit_proof_line(proof_step.str());
                    }});
                return Inference::Contradiction;
            }
        }

        return Inference::NoChange;
    }

    // Slightly more complex propagator: prevent small cycles by finding chains and removing the head from the domain
    // of the tail.
    auto propagate_circuit_using_prevent(vector<IntegerVariableID> succ, ProofLine2DMap lines_for_setting_pos, State& state) -> Inference {
        // Have to use check first
        auto inference_from_check = propagate_circuit_using_check(succ, lines_for_setting_pos, state);
        if (inference_from_check == Inference::Contradiction) return Inference::Contradiction;

        vector<bool> checked(succ.size(), false);

        auto inference_from_prevent = Inference::NoChange;
        // Assume all different has already been propagated (do we know this for sure ???)
        for(const auto & [idx, var]: enumerate(succ)) {
            if(state.has_single_value(var)) continue;

            // In that case the possible start points for chains are the domains of the unfixed variables
            state.for_each_value_while(var, [&](auto val) {
                if(checked[val.raw_value]) return true; // Followed this chain already
                checked[val.raw_value] = true;

                auto current_val = state.optional_single_value(succ[val.raw_value]);
                auto chain_length = 1;
                auto next_var = var;

                stringstream proof_step;
                proof_step << "p ";

                if(current_val == nullopt) return true;

                proof_step << lines_for_setting_pos.at(make_pair(current_val.value(), val)) + 1 << " ";
                auto last_val = current_val;

                // Follow this chain to the end
                while(current_val != nullopt) {
                    last_val = current_val;
                    next_var = succ[last_val->raw_value];
                    current_val = state.optional_single_value(next_var);
                    chain_length ++;
                    if(current_val != nullopt) {
                        proof_step << lines_for_setting_pos.at(make_pair(current_val.value(), last_val.value())) + 1
                                   << " + ";
                    }
                }

                // Got the end of the chain, so infer that we cannot complete it to make a cycle, unless it has
                // visited all the nodes.
                auto infer_lit = chain_length < succ.size() ? next_var != val : next_var == val;

                switch(state.infer(infer_lit,
                    JustifyExplicitly{[&](Proof & proof, vector<ProofLine> &) -> void {
                        proof_step << lines_for_setting_pos.at(make_pair(val, last_val.value())) + 1
                                    << " + ";
                        proof.emit_proof_line(proof_step.str());
                    }})
                ) {
                    case Inference::Contradiction:
                        inference_from_prevent = Inference::Contradiction;
                        return false;
                    case Inference::Change:
                        inference_from_prevent = Inference::Change;
                        return true;
                    case Inference::NoChange:
                        return true;
                }
            });
        }

        return inference_from_prevent;
    }
}

auto Circuit::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Circuit>(_succ, _propagate_using_check_only);
}

auto Circuit::install(Propagators & propagators, const State & initial_state) && -> void
{
    // First define an all different constraint
    AllDifferent all_diff{_succ};
    move(all_diff).install(propagators, initial_state);
    ProofLine2DMap lines_for_setting_pos{};
    if (propagators.want_definitions()) {
        // Define encoding to eliminate sub-cycles
        vector<ProofOnlySimpleIntegerVariableID> position;
        auto n_minus_1 = ConstantIntegerVariableID{Integer{static_cast<long long>(_succ.size()-1)}};

        // Need extra proof variable: pos[i] = j means "the ith node visited in the circuit is the jth var"
        // WLOG start at node 0, so pos[0] = 0
        position.emplace_back(propagators.create_proof_only_integer_variable(0_i, 0_i, "pos0"));
        // Hence we can only have succ[0] = 0 (self cycle) if there is only one node i.e. n - 1 = 0
        auto cv = WeightedPseudoBooleanTerms{{1_i, position[0]}, {-1_i, n_minus_1}};
        auto proof_line = propagators.define_pseudoboolean_eq(initial_state, move(cv), 0_i, _succ[0] == 0_i);
        lines_for_setting_pos.insert({{Integer{0_i}, Integer{0_i}}, proof_line.value_or(0)});

        for(unsigned int idx = 1; idx < _succ.size(); ++idx) {
            position.emplace_back(propagators.create_proof_only_integer_variable(0_i, Integer(_succ.size() - 1), "pos" + to_string(idx)));
        }

        for(unsigned int idx = 1; idx < _succ.size(); ++idx) {
            // (succ[0] = i) -> pos[i] = 1
            auto cv1 = WeightedPseudoBooleanTerms{{1_i, position[idx]}, {-1_i, 1_c}};
            auto proof_line = propagators.define_pseudoboolean_eq(initial_state, move(cv1), 0_i, _succ[0] == Integer{idx});
            lines_for_setting_pos.insert({{Integer{idx}, Integer{0_i}}, proof_line.value_or(0)});

            // (succ[i] = 0) -> pos[i] = n-1
            auto cv2 = WeightedPseudoBooleanTerms{{1_i, position[idx]}, {-1_i, n_minus_1}};

            proof_line = propagators.define_pseudoboolean_eq(initial_state, move(cv2), 0_i, _succ[idx] == 0_i);
            lines_for_setting_pos.insert({{Integer{0_i}, Integer{idx}}, proof_line.value_or(0)});

            // (succ[i] = j) -> pos[j] = pos[i] + 1
            for(unsigned int jdx = 1; jdx < _succ.size(); ++jdx) {
                //if (idx == jdx) continue;
                auto cv3 = WeightedPseudoBooleanTerms{{1_i, position[jdx]}, {-1_i, position[idx]}, {-1_i, 1_c}};

                proof_line = propagators.define_pseudoboolean_eq(initial_state, move(cv3), 0_i, _succ[idx] == Integer{jdx});
                lines_for_setting_pos.insert({{Integer{jdx}, Integer{idx}}, proof_line.value_or(0)});
            }
        }

        // For basic "check" algorithm, only trigger when variable gains a unique value
        Triggers triggers;
        triggers.on_instantiated = {_succ.begin(), _succ.end()};

        propagators.install(
            initial_state,
            [succ = _succ, use_check = _propagate_using_check_only, lines_for_setting_pos = lines_for_setting_pos](State & state) -> pair<Inference, PropagatorState>
            {
                return pair{
                    use_check ? propagate_circuit_using_check(succ, lines_for_setting_pos, state) : propagate_circuit_using_prevent(succ, lines_for_setting_pos, state),
                    PropagatorState::Enable};
            },
            triggers,
            "circuit"
        );

    }
}

auto Circuit::describe_for_proof() -> std::string
{
    return "circuit (all different + no sub-cycles)";
}