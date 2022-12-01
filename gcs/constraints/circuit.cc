#include <gcs/constraints/circuit.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/constraints/all_different.hh>

#include <util/enumerate.hh>

#include <utility>
#include <iostream>
using namespace gcs;
using namespace gcs::innards;

using std::vector;
using std::move;
using std::nullopt;
using std::to_string;
using std::pair;


Circuit::Circuit(const vector<IntegerVariableID> & v) :
    _succ(v)
{
}

namespace {
    // Very rubbish basic propagator to get started with
    auto propagate_circuit_using_check(vector<IntegerVariableID> succ, State& state) -> Inference {
        vector<bool> checked(succ.size(), false);
        for(const auto & [idx, var]: enumerate(succ)) {
            if(checked[idx]) continue;

            checked[idx] = true;
            auto fixed_val = state.optional_single_value(var);
            if(fixed_val == nullopt) continue;
            if(fixed_val->raw_value < 0) {
                return Inference::Contradiction;
            }
            bool finished_cycle = true;
            unsigned long cycle_length = 1;

            while(fixed_val->raw_value != idx) {
                auto next_var = succ[fixed_val->raw_value];
                fixed_val = state.optional_single_value(next_var);

                if(fixed_val == nullopt) {
                    finished_cycle = false;
                    break;
                }

                checked[fixed_val->raw_value] = true;

                cycle_length++;
            }


            if(finished_cycle && cycle_length < succ.size()) {
                return Inference::Contradiction;
            }
        }

        return Inference::NoChange;
    }
}

auto Circuit::install(Propagators & propagators, const State & initial_state) && -> void
{
    // First define an all different constraint
    AllDifferent all_diff{_succ};
    move(all_diff).install(propagators, initial_state);

    if (propagators.want_definitions()) {
        // Define encoding to eliminate sub-cycles
        vector<IntegerVariableID> position;
        auto constN = ConstantIntegerVariableID{Integer{static_cast<long long>(_succ.size()-1)}};

        // Need extra proof variable: pos[i] = j means "the ith node visited in the circuit is the jth var"
        // WLOG start at node 0, so pos[0] = [0]
        position.emplace_back(propagators.create_proof_only_variable(0_i, 0_i, "pos0"));
        auto cv = Linear{{1_i, position[0]}, {-1_i, constN}};
        propagators.define_linear_eq(initial_state, cv, 0_i, _succ[0] == 0_i);

        for(unsigned int idx = 1; idx < _succ.size(); ++idx) {
            position.emplace_back(propagators.create_proof_only_variable(0_i, Integer(_succ.size() - 1), "pos" + to_string(idx)));
        }

        for(unsigned int idx = 1; idx < _succ.size(); ++idx) {
            // (succ[0] = i) -> pos[i] = 1
            auto cv1 = Linear{{1_i, position[idx]}, {-1_i, 1_c}};
            propagators.define_linear_eq(initial_state, cv1, 0_i, _succ[0] == Integer{idx});

            // (succ[i] = 0) -> pos[i] = n-1
            auto cv2 = Linear{{1_i, position[idx]}, {-1_i, constN}};
            propagators.define_linear_eq(initial_state, cv2, 0_i, _succ[idx] == 0_i);

            // (succ[i] = j) -> pos[j] = pos[i] + 1
            for(unsigned int jdx = 1; jdx < _succ.size(); ++jdx) {
                //if (idx == jdx) continue;
                auto cv3 = Linear{{1_i, position[jdx]}, {-1_i, position[idx]}, {-1_i, 1_c}};
                propagators.define_linear_eq(initial_state, cv3, 0_i, _succ[idx] == Integer{jdx});
            }
        }

        // For basic "check" algorithm, only trigger when variable gains a unique value
        Triggers triggers;
        triggers.on_instantiated = {_succ.begin(), _succ.end()};

        propagators.install(
            initial_state,
            [succ = _succ](State & state) -> pair<Inference, PropagatorState>
            {
                return pair{
                    propagate_circuit_using_check(succ, state),
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