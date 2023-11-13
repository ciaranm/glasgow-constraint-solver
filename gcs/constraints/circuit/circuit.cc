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
    const PosVarDataMap & pos_var_data,
    State & state,
    Proof & proof,
    const optional<Integer> & prevent_idx,
    const optional<Integer> & prevent_value) -> void
{

    auto current_val = state.optional_single_value(succ[start]);
    if (current_val == nullopt)
        throw UnexpectedException("Circuit propagator tried to output a cycle that doesn't exist");

    if (current_val->raw_value < 0)
        throw UnimplementedException("Successor encoding for circuit can't have negative values");

    stringstream proof_step;

    proof_step << "p ";
    proof_step << pos_var_data.at(start).plus_one_lines.at(current_val->raw_value).geq_line << " ";
    long cycle_length = 1;
    while (cmp_not_equal(current_val->raw_value, start)) {
        auto last_val = current_val;
        auto next_var = succ[last_val->raw_value];
        current_val = state.optional_single_value(next_var);

        if (current_val == nullopt || cycle_length == length) break;

        proof_step << pos_var_data.at(last_val->raw_value).plus_one_lines.at(current_val->raw_value).geq_line
                   << " + ";
        cycle_length++;
    }

    if (prevent_idx.has_value()) {
        proof.emit_proof_comment("Preventing sub-cycle for succ[" + to_string(prevent_idx->raw_value) + "] = " + to_string(prevent_value->raw_value));
        proof_step << pos_var_data.at(prevent_idx->raw_value).plus_one_lines.at(prevent_value->raw_value).geq_line
                   << " + ";
    }
    else {
        proof.emit_proof_comment("Contradicting sub-cycle");
    }

    proof.emit_proof_line(proof_step.str(), ProofLevel::Current);
}

auto gcs::prevent_small_cycles(
    const vector<IntegerVariableID> & succ,
    const PosVarDataMap & pos_var_data,
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
            state.infer(succ[end[i]] != Integer{i}, JustifyExplicitly{[&](Proof & proof) {
                output_cycle_to_proof(succ, i, length, pos_var_data, state, proof, Integer{end[i]}, Integer{i});
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

auto CircuitBase::set_up(Propagators & propagators, State & initial_state) -> PosVarDataMap
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
    PosVarDataMap pos_var_data{};

    if (propagators.want_definitions()) {

        auto n = static_cast<long long>(_succ.size());
        // Define encoding to eliminate sub-cycles
        // Need extra proof variable: pos[i] = j means "the ith node visited in the circuit is the jth var"
        // WLOG start at node 0, so pos[0] = 0
        pos_var_data.emplace(0,
            PosVarData{"p[0]", propagators.create_proof_only_integer_variable(0_i, Integer{n - 1}, "pos" + to_string(0), IntegerVariableProofRepresentation::Bits), map<long, PosVarLineData>{}});
        propagators.define(initial_state, WeightedPseudoBooleanSum{} + 1_i * pos_var_data.at(0).var <= 0_i);
        // Hence we can only have succ[0] = 0 (self cycle) if there is only one node i.e. n - 1 = 0
        auto [leq_line, geq_line] = propagators.define(initial_state,
            WeightedPseudoBooleanSum{} == Integer{n - 1},
            HalfReifyOnConjunctionOf{{_succ[0] == 0_i}});

        pos_var_data.at(0).plus_one_lines.emplace(0, PosVarLineData{leq_line.value(), geq_line.value()});

        for (unsigned int idx = 1; idx < _succ.size(); ++idx) {
            pos_var_data.emplace(idx,
                PosVarData{"p[" + to_string(idx) + "]", propagators.create_proof_only_integer_variable(0_i, Integer{n - 1}, "pos" + to_string(0), IntegerVariableProofRepresentation::Bits), map<long, PosVarLineData>{}});
        }

        for (unsigned int idx = 1; idx < _succ.size(); ++idx) {
            // (succ[0] = i) -> pos[i] - pos[0] = 1
            tie(leq_line, geq_line) = propagators.define(initial_state,
                WeightedPseudoBooleanSum{} + 1_i * pos_var_data.at(idx).var + -1_i * 1_c == 0_i,
                HalfReifyOnConjunctionOf{{_succ[0] == Integer{idx}}});
            pos_var_data.at(0).plus_one_lines.emplace(idx, PosVarLineData{leq_line.value(), geq_line.value()});

            // (succ[i] = 0) -> pos[0] - pos[i] = 1-n
            tie(leq_line, geq_line) = propagators.define(
                initial_state,
                WeightedPseudoBooleanSum{} + 1_i * pos_var_data.at(0).var + -1_i * pos_var_data.at(idx).var == Integer{1 - n},
                HalfReifyOnConjunctionOf{{_succ[idx] == 0_i}});
            pos_var_data.at(idx).plus_one_lines.emplace(0, PosVarLineData{leq_line.value(), geq_line.value()});

            // (succ[i] = j) -> pos[j] = pos[i] + 1
            for (unsigned int jdx = 1; jdx < _succ.size(); ++jdx) {
                tie(leq_line, geq_line) = propagators.define(initial_state,
                    WeightedPseudoBooleanSum{} + 1_i * pos_var_data.at(jdx).var + -1_i * pos_var_data.at(idx).var == 1_i,
                    HalfReifyOnConjunctionOf{{_succ[idx] == Integer{jdx}}});
                pos_var_data.at(idx).plus_one_lines.emplace(jdx, PosVarLineData{leq_line.value(), geq_line.value()});
            }
        }
    }

    // Infer succ[i] != i at top of search, but no other propagation defined here: use CircuitPrevent or CircuitSCC
    if (_succ.size() > 1) {
        propagators.install([succ = _succ](State & state) -> pair<Inference, PropagatorState> {
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

    return pos_var_data;
}

auto CircuitBase::describe_for_proof() -> std::string
{
    return "circuit (all different + no sub-cycles)";
}
