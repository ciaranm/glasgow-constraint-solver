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

auto check_small_cycles(const vector<IntegerVariableID> & succ, State & state) -> Inference
{
    auto n = succ.size();
    auto checked = vector<bool>(n, false);
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
                        if (cycle_length < n)
                            return Inference::Contradiction;
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
    const ProofLine2DMap & lines_for_setting_pos,
    const ConstraintStateHandle & unassigned_handle,
    const vector<ProofOnlySimpleIntegerVariableID> & pos_vars,
    State & state)
{
    auto result = propagate_non_gac_alldifferent(unassigned_handle, state);
    if (result == Inference::Contradiction) return result;
    increase_inference_to(result, check_small_cycles(succ, state));
    if (result == Inference::Contradiction) return result;
    increase_inference_to(result, prevent_small_cycles(succ, lines_for_setting_pos, unassigned_handle, pos_vars, state));
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
    auto lines_for_setting_pos = get<1>(set_up_results);
    auto unassigned_handle = get<2>(set_up_results);

    Triggers triggers;
    triggers.on_instantiated = {_succ.begin(), _succ.end()};
    propagators.install(
        [succ = _succ, pos_vars = pos_vars, lines_for_setting_pos = lines_for_setting_pos,
            unassigned_handle = unassigned_handle](State & state) -> pair<Inference, PropagatorState> {
            return pair{
                propagate_circuit_using_prevent(succ, lines_for_setting_pos, unassigned_handle, pos_vars, state),
                PropagatorState::Enable};
        },
        triggers,
        "circuit");
}
