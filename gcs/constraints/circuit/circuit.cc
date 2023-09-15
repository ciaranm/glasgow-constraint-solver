#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/circuit/circuit.hh>
#include <gcs/innards/propagators.hh>

#include <iostream>
#include <list>
#include <map>
#include <sstream>
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
    _succ(std::move(v))
{
}

auto gcs::output_cycle_to_proof(const vector<IntegerVariableID> & succ,
    const long & start,
    const long & length,
    const ProofLine2DMap & lines_for_setting_pos,
    State & state,
    Proof & proof,
    vector<ProofLine> & to_delete,
    const optional<Integer> & prevent_idx,
    const optional<Integer> & prevent_value) -> void
{

    auto current_val = state.optional_single_value(succ[start]);
    if (current_val == nullopt)
        throw UnexpectedException("Circuit propagator tried to output a cycle that doesn't exist");

    if (current_val->raw_value < 0)
        throw UnimplementedException("Successor encoding for circuit can't have negative values");

    stringstream proof_step;

    if (state.maybe_proof()) {
        proof_step << "p ";
        proof_step << lines_for_setting_pos.at(make_pair(current_val.value(), Integer(start))) << " ";
    }
    long cycle_length = 1;
    while (cmp_not_equal(current_val->raw_value, start)) {
        auto last_val = current_val;
        auto next_var = succ[last_val->raw_value];
        current_val = state.optional_single_value(next_var);

        if (current_val == nullopt || cycle_length == length - 1) break;

        proof_step << lines_for_setting_pos.at(make_pair(current_val.value(), last_val.value()))
                   << " + ";
        cycle_length++;
    }

    if (prevent_idx.has_value()) {
        proof_step << lines_for_setting_pos.at(make_pair(prevent_value.value(), prevent_idx.value()))
                   << " + ";
    }

    to_delete.push_back(proof.emit_proof_line(proof_step.str()));
}

auto gcs::prevent_small_cycles(
    const vector<IntegerVariableID> & succ,
    const ProofLine2DMap & lines_for_setting_pos,
    const ConstraintStateHandle & unassigned_handle,
    State & state) -> Inference
{

    auto result = Inference::NoChange;
    auto & unassigned = any_cast<list<IntegerVariableID> &>(state.get_constraint_state(unassigned_handle));
    auto n = succ.size();
    auto end = vector<long>(n, -1);
    auto known_ends = vector<long>{};
    auto cycle_lengths = vector<long>{};

    for (auto var : unassigned) {
        state.for_each_value(var, [&](Integer val) {
            auto j0 = val.raw_value;
            auto length = 0;
            if (state.has_single_value(succ[j0]) && (end[j0] < 0)) {
                auto j = j0;
                do {
                    j = state.optional_single_value(succ[j])->raw_value;
                    length++;
                } while (state.has_single_value(succ[j]));
                end[j0] = j;
                known_ends.emplace_back(j0);
                cycle_lengths.emplace_back(length);
            }
        });
    }

    while (! known_ends.empty()) {
        auto i = known_ends.back();
        known_ends.pop_back();
        auto length = cycle_lengths.back();
        cycle_lengths.pop_back();
        increase_inference_to(result,
            state.infer(succ[end[i]] != Integer{i}, JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & to_delete) {
                output_cycle_to_proof(succ, i, length, lines_for_setting_pos, state, proof, to_delete, Integer{end[i]}, Integer{i});
            }}));
    }
    return result;
}

auto gcs::propagate_non_gac_alldifferent(const ConstraintStateHandle & unassigned_handle, State & state) -> innards::Inference
{
    auto & unassigned = any_cast<list<IntegerVariableID> &>(state.get_constraint_state(unassigned_handle));

    auto result = Inference::NoChange;
    vector<pair<IntegerVariableID, Integer>> to_propagate;
    {
        // Collect any newly assigned values
        auto i = unassigned.begin();
        while (i != unassigned.end()) {
            auto s = *i;
            if (auto val = state.optional_single_value(s)) {
                to_propagate.emplace_back(s, *val);
                unassigned.erase(i++);
            }
            else
                ++i;
        }
    }

    while (! to_propagate.empty()) {
        auto [var, val] = to_propagate.back();
        to_propagate.pop_back();
        auto i = unassigned.begin();

        for (auto other : to_propagate) {
            if (other.second == val) return Inference::Contradiction;
        }

        while (i != unassigned.end()) {
            auto other = *i;
            if (other != var) {
                increase_inference_to(result, state.infer_not_equal(other, val, JustifyUsingRUP{}));
                if (result == Inference::Contradiction) return Inference::Contradiction;
                if (auto other_val = state.optional_single_value(other)) {
                    to_propagate.emplace_back(other, *other_val);
                    unassigned.erase(i++);
                }
                else
                    ++i;
            }
        }
    }
    return result;
}

auto CircuitBase::set_up(Propagators & propagators, State & initial_state) -> pair<vector<ProofOnlySimpleIntegerVariableID>, ProofLine2DMap>
{
    // Can't have negative values
    for (const auto & s : _succ)
        propagators.trim_lower_bound(initial_state, s, 0_i, "Circuit");

    // Can't have too-large values
    for (const auto & s : _succ)
        propagators.trim_upper_bound(initial_state, s, Integer(static_cast<long long>(_succ.size() - 1)), "Circuit");

    // Define all different, either gac or non-gac
    if (_gac_all_different) {
        AllDifferent all_diff{_succ};
        std::move(all_diff).install(propagators, initial_state);
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
        auto n_minus_1 = Integer{static_cast<long long>(_succ.size() - 1)};
        auto n_minus_1_var = ConstantIntegerVariableID{n_minus_1};

        // Need extra proof variable: pos[i] = j means "the ith node visited in the circuit is the jth var"
        // WLOG start at node 0, so pos[0] = 0
        position.emplace_back(propagators.create_proof_only_integer_variable(0_i, n_minus_1,
            "pos" + to_string(0), IntegerVariableProofRepresentation::Bits));
        propagators.define(initial_state, WeightedPseudoBooleanSum{} + 1_i * position[0] == 0_i);

        // Hence we can only have succ[0] = 0 (self cycle) if there is only one node i.e. n - 1 = 0
        auto proof_line = propagators.define(initial_state,
            WeightedPseudoBooleanSum{} + 1_i * position[0] + -1_i * n_minus_1_var == 0_i,
            HalfReifyOnConjunctionOf{{_succ[0] == 0_i}});
        lines_for_setting_pos.insert({{Integer{0_i}, Integer{0_i}}, proof_line.second.value()});

        for (unsigned int idx = 1; idx < _succ.size(); ++idx) {
            position.emplace_back(propagators.create_proof_only_integer_variable(0_i, n_minus_1,
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
                WeightedPseudoBooleanSum{} + 1_i * position[idx] + -1_i * n_minus_1_var == 0_i,
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
                increase_inference_to(result, state.infer_not_equal(s, Integer(static_cast<long long>(idx)), JustifyUsingRUP{}));
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

