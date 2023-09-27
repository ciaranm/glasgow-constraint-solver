
#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/circuit/circuit.hh>
#include <gcs/innards/propagators.hh>
#include <map>
#include <util/enumerate.hh>
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

// Constraint states for prevent algorithm
struct Chain
{
    vector<long long> start;
    vector<long long> end;
    vector<long long> length;
};

namespace
{
    auto propagate_non_gac_alldifferent_single(const optional<IntegerVariableID> & trigger_var,
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

    // Slightly more complex propagator: prevent small cycles by finding chains and removing the head from the domain
    // of the tail.
    auto propagate_circuit_using_incremental_prevent(const vector<IntegerVariableID> & succ,
        const PosVarDataMap & pos_var_data,
        State & state,
        const IntegerVariableID & trigger_var,
        const long & trigger_idx,
        const ConstraintStateHandle & chain_handle,
        bool & should_disable) -> Inference
    {
        // propagate all-different first, to avoid infinite loops
        // Have to use check first
        auto result = propagate_non_gac_alldifferent_single(trigger_var, succ, state);
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
            state.infer_false(JustifyExplicitly{[&](Proof & proof) -> void {
                proof.emit_proof_comment("Contradicting cycle");
                output_cycle_to_proof(succ, start, chain.length[start], pos_var_data, state, proof);
            }});
            if (state.maybe_proof())
                return Inference::Contradiction;
        }
        else {
            chain.length[start] += chain.length[next_idx];
            chain.start[end] = start;
            chain.end[start] = end;

            if (cmp_less(chain.length[start], succ.size())) {
                increase_inference_to(result, state.infer(succ[end] != Integer{start}, JustifyExplicitly{[&](Proof & proof) {
                    proof.emit_proof_comment("Preventing cycle");
                    output_cycle_to_proof(succ, start, chain.length[start], pos_var_data, state, proof, make_optional(Integer{end}),
                        make_optional(Integer{start}));
                    proof.infer(state, succ[end] != Integer{start}, JustifyUsingRUP{});
                    proof.emit_proof_comment("Done preventing cycle");
                }}));
            }
            else {
                state.infer_true(JustifyExplicitly{[&](Proof & proof) -> void {
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

auto CircuitPreventIncremental::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Circuit>(_succ, _gac_all_different);
}

auto CircuitPreventIncremental::install(Propagators & propagators, State & initial_state) && -> void
{
    auto pos_var_data = CircuitBase::set_up(propagators, initial_state);
    // Constraint states for incremental prevent algorithm

    Chain chain;

    for (unsigned int idx = 0; idx < _succ.size(); idx++) {
        chain.start.emplace_back(idx);
        chain.end.emplace_back(idx);
        chain.length.emplace_back(1);
    }

    auto chain_handle = initial_state.add_constraint_state(chain);

    for (auto [idx, var] : enumerate(_succ)) {
        Triggers triggers;
        triggers.on_instantiated = {var};
        propagators.install(
            [succ = _succ, v = var, i = idx, pvd = pos_var_data, chain_handle = chain_handle, want_proof = propagators.want_definitions()](State & state) -> pair<Inference, PropagatorState> {
                bool should_disable = false;
                auto result = propagate_circuit_using_incremental_prevent(
                    succ, pvd, state, v, static_cast<long>(i), chain_handle, should_disable);
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
                increase_inference_to(result, state.infer_not_equal(s, Integer(static_cast<long>(idx)), JustifyUsingRUP{}));
                if (result == Inference::Contradiction)
                    break;
            }
            return pair{result, PropagatorState::DisableUntilBacktrack};
        },
            Triggers{}, "circuit init");
    }
}
