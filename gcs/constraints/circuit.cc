#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/circuit.hh>
#include <gcs/exception.hh>
#include <gcs/innards/propagators.hh>

#include <util/enumerate.hh>

#include <map>
#include <sstream>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::cmp_less;
using std::cmp_not_equal;
using std::make_optional;
using std::make_pair;
using std::map;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::size_t;
using std::stringstream;
using std::to_string;
using std::unique_ptr;
using std::vector;

using ProofLine2DMap = map<pair<Integer, Integer>, ProofLine>;

// Constraint states for prevent algorithm
struct Chain
{
    vector<long long> start;
    vector<long long> end;
    vector<long long> length;
};

Circuit::Circuit(vector<IntegerVariableID> v, const bool g) :
    _succ(move(v)),
    _gac_all_different(g)
{
}

namespace
{
    auto propagate_non_gac_alldifferent(const optional<IntegerVariableID> & trigger_var,
        const vector<IntegerVariableID> & succ, State & state) -> Inference
    {
        auto result = Inference::NoChange;
        if (trigger_var) {
            auto val = state.optional_single_value(*trigger_var);
            if (val) {
                for (auto [other_idx, other] : enumerate(succ))
                    if (other != *trigger_var) {
                        increase_inference_to(result, state.infer_not_equal(other, *val, JustifyUsingRUP{}));
                        if (result == Inference::Contradiction) return Inference::Contradiction;
                    }
            }
        }
        return result;
    }

    auto output_cycle_to_proof(const vector<IntegerVariableID> & succ,
        const long & start,
        const long & length,
        const ProofLine2DMap & lines_for_setting_pos,
        State & state,
        Proof & proof,
        vector<ProofLine> & to_delete,
        const optional<Integer> & prevent_idx = nullopt,
        const optional<Integer> & prevent_value = nullopt) -> void
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

    // Slightly more complex propagator: prevent small cycles by finding chains and removing the head from the domain
    // of the tail.
    auto propagate_circuit_using_prevent(const vector<IntegerVariableID> & succ,
        const ProofLine2DMap & lines_for_setting_pos,
        State & state,
        const IntegerVariableID & trigger_var,
        const long & trigger_idx,
        const ConstraintStateHandle & chain_handle,
        bool & should_disable) -> Inference
    {
        // propagate all-different first, to avoid infinite loops
        // Have to use check first
        auto result = propagate_non_gac_alldifferent(trigger_var, succ, state);
        if (result == Inference::Contradiction) return Inference::Contradiction;

        auto & chain = any_cast<Chain &>(state.get_constraint_state(chain_handle));
        auto n = succ.size();

        auto current_idx = trigger_idx;
        auto var = trigger_var;
        auto value = state.optional_single_value(var);
        if (value == nullopt)
            return result;
        auto start = chain.start[current_idx];
        auto next_idx = value->raw_value;
        auto end = chain.end[next_idx];

        if (cmp_not_equal(chain.length[start], n) && next_idx == start) {
            state.infer_false(JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & to_delete) -> void {
                proof.emit_proof_comment("Contradicting cycle");
                output_cycle_to_proof(succ, start, chain.length[start], lines_for_setting_pos, state, proof, to_delete);
            }});
            if (state.maybe_proof())
                return Inference::Contradiction;
        }
        else {
            chain.length[start] += chain.length[next_idx];
            chain.start[end] = start;
            chain.end[start] = end;

            if (cmp_less(chain.length[start], succ.size())) {
                increase_inference_to(result, state.infer(succ[end] != Integer{start}, JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & to_delete) {
                    proof.emit_proof_comment("Preventing cycle");
                    output_cycle_to_proof(succ, start, chain.length[start], lines_for_setting_pos, state, proof, to_delete, make_optional(Integer{end}),
                        make_optional(Integer{start}));
                    proof.infer(state, succ[end] != Integer{start}, JustifyUsingRUP{});
                    proof.emit_proof_comment("Done preventing cycle");
                }}));
            }
            else {
                state.infer_true(JustifyExplicitly{[&](Proof & proof, vector<ProofLine> &) -> void {
                    proof.emit_proof_comment("Completing cycle");
                }});
                increase_inference_to(result, state.infer(succ[end] == Integer{start}, JustifyUsingRUP{}));
                return result;
            }

            if (result == Inference::Contradiction) {
                return Inference::Contradiction;
            }

            if (state.optional_single_value(succ[end])) {
                should_disable = true;
            }
        }
        return result;
    }
}

auto Circuit::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Circuit>(_succ, _gac_all_different);
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
                propagators.define(initial_state, WeightedPseudoBooleanSum{} + 1_i * _succ[i] + -1_i * _succ[j] <= -1_i,
                    HalfReifyOnConjunctionOf{selector});
                propagators.define(initial_state, WeightedPseudoBooleanSum{} + -1_i * _succ[i] + 1_i * _succ[j] <= -1_i,
                    HalfReifyOnConjunctionOf{! selector});
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

    // Constraint states for prevent algorithm

    Chain chain;

    for (unsigned int idx = 0; idx < _succ.size(); idx++) {
        chain.start.emplace_back(idx);
        chain.end.emplace_back(idx);
        chain.length.emplace_back(1);
    }

    auto chain_handle = initial_state.add_constraint_state(chain);

    for (unsigned int idx = 0; idx < _succ.size(); idx++) {
        Triggers triggers;
        triggers.on_instantiated = {_succ[idx]};
        propagators.install(
            [succ = _succ, idx = idx, lines_for_setting_pos = lines_for_setting_pos, chain_handle = chain_handle, want_proof = propagators.want_definitions()](State & state) -> pair<Inference, PropagatorState> {
                bool should_disable = false;
                auto result = propagate_circuit_using_prevent(
                    succ, lines_for_setting_pos, state, succ[idx], idx, chain_handle, should_disable);
                return pair{
                    result,
                    should_disable ? PropagatorState::DisableUntilBacktrack : PropagatorState::Enable};
            },
            triggers,
            "circuit");
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
