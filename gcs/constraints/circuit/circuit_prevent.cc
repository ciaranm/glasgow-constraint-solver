#include <gcs/constraints/circuit/circuit.hh>
#include <gcs/exception.hh>
#include <gcs/innards/propagators.hh>

#include <util/enumerate.hh>

#include <list>
#include <map>
#include <sstream>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::cmp_less;
using std::cmp_not_equal;
using std::get;
using std::list;
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

auto check_small_cycles(const vector<IntegerVariableID> & succ, const ConstraintStateHandle & line_for_starting_cycle_handle,
    const vector<ProofOnlySimpleIntegerVariableID> & pos_vars, State & state) -> Inference
{
    auto n = succ.size();
    auto checked = vector<bool>(n, false);
    auto & line_for_starting_cycle = any_cast<long &>(state.get_persistent_constraint_state(line_for_starting_cycle_handle));
    for (auto [idx, var] : enumerate(succ)) {
        if (checked[idx]) continue;
        checked[idx] = true;
        if (auto val = state.optional_single_value(var)) {
            auto j0 = (*val).raw_value;
            if (state.has_single_value(succ[j0])) {
                size_t cycle_length = 0;
                auto j = j0;
                do {
                    j = state.optional_single_value(succ[j])->raw_value;
                    checked[j] = true;
                    cycle_length++;
                    if (j == j0) {
                        if (cycle_length < n) {
                            state.infer_true(JustifyExplicitly{[&](Proof & proof, vector<ProofLine> & to_delete) {
                                if (line_for_starting_cycle != -1) {
                                    proof.delete_proof_lines({line_for_starting_cycle});
                                }
                                auto previous_proof_level = proof.get_proof_level();
                                proof.enter_proof_level(0);
                                proof.emit_proof_comment("Starting cycle for check");
                                line_for_starting_cycle = proof.emit_assertion_proof_line(WeightedPseudoBooleanSum{} + 1_i * (pos_vars[j0] == 0_i) >= 1_i);
                                proof.enter_proof_level(previous_proof_level);
                            }});
                            return Inference::Contradiction;
                        }

                        else
                            break;
                    }
                } while (state.has_single_value(succ[j]));
            }
        }
    }
    return Inference::NoChange;
}

auto propagate_circuit_using_prevent(
    const vector<IntegerVariableID> & succ,
    const ConstraintStateHandle & line_for_starting_cycle_handle,
    const ConstraintStateHandle & unassigned_handle,
    const vector<ProofOnlySimpleIntegerVariableID> & pos_vars,
    State & state)
{
    auto result = propagate_non_gac_alldifferent(unassigned_handle, state);
    if (result == Inference::Contradiction) return result;
    increase_inference_to(result, check_small_cycles(succ, line_for_starting_cycle_handle, pos_vars, state));
    if (result == Inference::Contradiction) return result;
    increase_inference_to(result, prevent_small_cycles(succ, line_for_starting_cycle_handle, unassigned_handle, pos_vars, state));
    return result;
}

auto CircuitPrevent::clone() const -> unique_ptr<Constraint>
{
    return make_unique<CircuitPrevent>(_succ, _gac_all_different);
}

auto CircuitPrevent::install(Propagators & propagators, State & initial_state) && -> void
{
    auto set_up_results = CircuitBase::set_up(propagators, initial_state);
    auto pos_vars = get<0>(set_up_results);
    auto line_for_starting_cycle = get<1>(set_up_results);
    auto unassigned_handle = get<2>(set_up_results);

    Triggers triggers;
    triggers.on_instantiated = {_succ.begin(), _succ.end()};
    propagators.install(
        [succ = _succ, pos_vars = pos_vars, line_for_starting_cycle = line_for_starting_cycle,
            unassigned_handle = unassigned_handle](State & state) -> pair<Inference, PropagatorState> {
            return pair{
                propagate_circuit_using_prevent(succ, line_for_starting_cycle, unassigned_handle, pos_vars, state),
                PropagatorState::Enable};
        },
        triggers,
        "circuit");
}
