#include <gcs/constraints/all_different/vc_all_different.hh>
#include <gcs/constraints/circuit/circuit_base.hh>
#include <gcs/constraints/circuit/circuit_prevent.hh>

#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/propagators.hh>

#include <util/enumerate.hh>

#include <list>
#include <map>
#include <utility>

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::innards::circuit;

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

namespace
{
    auto check_small_cycles(const vector<IntegerVariableID> & succ, const PosVarDataMap & pos_var_data, const State & state,
        auto & inference, ProofLogger * const logger) -> void
    {
        auto n = succ.size();
        auto checked = vector<bool>(n, false);

        for (auto [idx, var] : enumerate(succ)) {
            if (checked[idx]) continue;
            checked[idx] = true;
            if (auto val = state.optional_single_value(var)) {
                auto j0 = (*val).raw_value;
                if (state.has_single_value(succ[j0])) {
                    auto cycle_length = 0;
                    auto j = j0;
                    do {
                        j = state.optional_single_value(succ[j])->raw_value;
                        checked[j] = true;
                        cycle_length++;
                        if (j == j0) {
                            if (cmp_less(cycle_length, n)) {
                                if (logger)
                                    output_cycle_to_proof(succ, j0, cycle_length, pos_var_data, state, *logger);
                                inference.contradiction(logger, JustifyUsingRUP{}, AllVariablesExactValues{});
                            }

                            else
                                break;
                        }
                    } while (state.has_single_value(succ[j]));
                }
            }
        }
    }

    auto propagate_circuit_using_prevent(
        const vector<IntegerVariableID> & succ,
        const PosVarDataMap & pos_var_data,
        const ConstraintStateHandle & unassigned_handle,
        const State & state,
        auto & inference,
        ProofLogger * const logger) -> void
    {
        propagate_non_gac_alldifferent(unassigned_handle, state, inference, logger);
        check_small_cycles(succ, pos_var_data, state, inference, logger);
        prevent_small_cycles(succ, pos_var_data, unassigned_handle, state, inference, logger);
    }
}

auto CircuitPrevent::clone() const -> unique_ptr<Constraint>
{
    return make_unique<CircuitPrevent>(_succ, _gac_all_different);
}

auto CircuitPrevent::install(innards::Propagators & propagators, innards::State & initial_state,
    innards::ProofModel * const model) && -> void
{
    // Keep track of unassigned vars
    list<IntegerVariableID> unassigned{};
    for (auto v : _succ) {
        unassigned.emplace_back(v);
    }
    auto unassigned_handle = initial_state.add_constraint_state(unassigned);

    auto pos_var_data = CircuitBase::set_up(propagators, initial_state, model);

    Triggers triggers;
    triggers.on_instantiated = {_succ.begin(), _succ.end()};
    propagators.install(
        [succ = _succ, pvd = pos_var_data,
            unassigned_handle = unassigned_handle](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            propagate_circuit_using_prevent(succ, pvd, unassigned_handle, state, inference, logger);
            return PropagatorState::Enable;
        },
        {_succ}, triggers, "circuit");
}
