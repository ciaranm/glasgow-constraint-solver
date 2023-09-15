#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/circuit/circuit.hh>
#include <gcs/innards/propagators.hh>

#include <iostream>
#include <list>
#include <map>
#include <string>
#include <util/enumerate.hh>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::cmp_less;
using std::cmp_not_equal;
using std::cout;
using std::endl;
using std::list;
using std::make_optional;
using std::make_pair;
using std::map;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::size_t;
using std::string;
using std::stringstream;
using std::to_string;
using std::tuple;
using std::unique_ptr;
using std::vector;

CircuitBase::CircuitBase(vector<IntegerVariableID> v, const bool g) :
    _gac_all_different(g),
    _succ(move(v))
{
}

auto CircuitBase::set_up(Propagators & propagators, State & initial_state) -> pair<vector<ProofOnlySimpleIntegerVariableID>, ProofLine2DMap>
{
    // Can't have negative values
    for (const auto & s : _succ)
        propagators.trim_lower_bound(initial_state, s, 0_i, "Circuit");

    // Can't have too-large values
    for (const auto & s : _succ)
        propagators.trim_upper_bound(initial_state, s, Integer(_succ.size() - 1), "Circuit");

    // Define all different, either gac or non-gac
    if (_gac_all_different) {
        AllDifferent all_diff{_succ};
        move(all_diff).install(propagators, initial_state);
    }
    else if (propagators.want_definitions()) {
        // Still need to define all-different
        for (unsigned i = 0; i < _succ.size(); ++i)
            for (unsigned j = i + 1; j < _succ.size(); ++j) {
                auto selector = propagators.create_proof_flag("circuit_notequals");
                propagators.define(initial_state, WeightedPseudoBooleanSum{} + 1_i * _succ[i] + -1_i * _succ[j] <= -1_i, HalfReifyOnConjunctionOf{selector});
                propagators.define(initial_state, WeightedPseudoBooleanSum{} + -1_i * _succ[i] + 1_i * _succ[j] <= -1_i, HalfReifyOnConjunctionOf{! selector});
            }
    }

    // Define encoding to eliminate sub-cycles
    ProofLine2DMap lines_for_setting_pos{};
    vector<ProofOnlySimpleIntegerVariableID> position;
    if (propagators.want_definitions()) {

        // Define encoding to eliminate sub-cycles
        auto n_minus_1 = ConstantIntegerVariableID{Integer{static_cast<long long>(_succ.size() - 1)}};

        // Need extra proof variable: pos[i] = j means "the ith node visited in the circuit is the jth var"
        // WLOG start at node 0, so pos[0] = 0
        position.emplace_back(propagators.create_proof_only_integer_variable(0_i, Integer(_succ.size() - 1),
            "pos" + to_string(0), IntegerVariableProofRepresentation::Bits));
        propagators.define(initial_state, WeightedPseudoBooleanSum{} + 1_i * position[0] == 0_i);

        // Hence we can only have succ[0] = 0 (self cycle) if there is only one node i.e. n - 1 = 0
        auto proof_line = propagators.define(initial_state,
            WeightedPseudoBooleanSum{} + 1_i * position[0] + -1_i * n_minus_1 == 0_i,
            HalfReifyOnConjunctionOf{{_succ[0] == 0_i}});
        lines_for_setting_pos.insert({{Integer{0_i}, Integer{0_i}}, proof_line.second.value()});

        for (unsigned int idx = 1; idx < _succ.size(); ++idx) {
            position.emplace_back(propagators.create_proof_only_integer_variable(0_i, Integer(_succ.size() - 1),
                "pos" + to_string(idx), IntegerVariableProofRepresentation::Bits));
        }

        for (unsigned int idx = 1; idx < _succ.size(); ++idx) {
            // (succ[0] = i) -> pos[i] = 1
            proof_line = propagators.define(initial_state,
                WeightedPseudoBooleanSum{} + 1_i * position[idx] + -1_i * 1_c == 0_i,
                HalfReifyOnConjunctionOf{{_succ[0] == Integer{idx}}});
            lines_for_setting_pos.insert({{Integer{idx}, Integer{0_i}}, proof_line.second.value()});

            // (succ[i] = 0) -> pos[i] = n-1
            proof_line = propagators.define(initial_state,
                WeightedPseudoBooleanSum{} + 1_i * position[idx] + -1_i * n_minus_1 == 0_i,
                HalfReifyOnConjunctionOf{{_succ[idx] == 0_i}});
            lines_for_setting_pos.insert({{Integer{0_i}, Integer{idx}}, proof_line.second.value()});

            // (succ[i] = j) -> pos[j] = pos[i] + 1
            for (unsigned int jdx = 1; jdx < _succ.size(); ++jdx) {
                proof_line = propagators.define(initial_state,
                    WeightedPseudoBooleanSum{} + 1_i * position[jdx] + -1_i * position[idx] + -1_i * 1_c == 0_i,
                    HalfReifyOnConjunctionOf{{_succ[idx] == Integer{jdx}}});
                lines_for_setting_pos.insert({{Integer{jdx}, Integer{idx}}, proof_line.second.value()});
            }
        }
    }

    // Infer succ[i] != i at top of search, but no other propagation defined here: use CircuitPrevent or CircuitSCC
    if (_succ.size() > 1) {
        propagators.install([succ = _succ, pos = position](State & state) -> pair<Inference, PropagatorState> {
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

    return pair{position, lines_for_setting_pos};
}

auto CircuitBase::describe_for_proof() -> std::string
{
    return "circuit (all different + no sub-cycles)";
}
