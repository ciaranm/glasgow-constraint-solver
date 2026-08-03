#include <gcs/constraints/cumulative/derived_cumulative.hh>
#include <gcs/constraints/cumulative/propagate.hh>
#include <gcs/exception.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <memory>
#include <string>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_shared;
using std::move;
using std::size_t;
using std::string;
using std::to_string;
using std::vector;

auto gcs::innards::install_derived_cumulative(
    Propagators & propagators, const State & initial_state, ProofLogger * const logger, DerivedCumulativeSpec spec) -> bool
{
    auto n = spec.starts.size();
    if (n != spec.lengths.size() || n != spec.heights.size())
        throw InvalidProblemDefinitionException{"derived Cumulative: starts, lengths, heights must have the same size"};
    if (spec.capacity < 0_i)
        throw InvalidProblemDefinitionException{"derived Cumulative: capacity must be non-negative"};
    for (size_t i = 0; i < n; ++i)
        if (spec.lengths[i] < 0_i || spec.heights[i] < 0_i)
            throw InvalidProblemDefinitionException{"derived Cumulative: lengths and heights must be non-negative"};
    if (! spec.recipe)
        throw InvalidProblemDefinitionException{"derived Cumulative: no recipe for deriving the capacity rows"};

    auto inputs = make_shared<CumulativeInputs>();
    inputs->owner = CurrentlyUnnamedConstraint{};
    inputs->starts = spec.starts;
    inputs->capacity = constant_variable(spec.capacity);
    inputs->rules = spec.rules;
    for (size_t i = 0; i < n; ++i) {
        inputs->lengths.push_back(constant_variable(spec.lengths[i]));
        inputs->heights.push_back(constant_variable(spec.heights[i]));
    }

    // The same windowing a posted Cumulative resolves in prepare(): a task can
    // be active from its earliest start to its latest finish, and one whose
    // length or height is zero never raises the profile at all.
    inputs->per_task_t_lo.assign(n, 0_i);
    vector<Integer> per_task_t_hi(n, 0_i);
    for (size_t i = 0; i < n; ++i) {
        if (spec.lengths[i] <= 0_i || spec.heights[i] <= 0_i)
            continue;
        inputs->active_tasks.push_back(i);
        auto [s_lo, s_hi] = initial_state.bounds(spec.starts[i]);
        inputs->per_task_t_lo[i] = s_lo;
        per_task_t_hi[i] = s_hi + spec.lengths[i] - 1_i;
    }

    if (inputs->active_tasks.empty())
        return false;

    if (spec.rules.overload) {
        auto overload_data = prepare_cumulative_overload_check(
            inputs->starts, inputs->lengths, inputs->heights, inputs->active_tasks, inputs->per_task_t_lo, per_task_t_hi, initial_state);
        inputs->overload_tasks = move(overload_data.overload_tasks);
        inputs->time_slot_prefix = move(overload_data.time_slot_prefix);
        inputs->time_slot_lo = overload_data.time_slot_lo;
    }

    // The donor's rows, to derive from. Resolved before anything is installed:
    // a derived constraint that cannot cite its donor must not be installed at
    // all, since its propagator would then be drawing inferences it has no way
    // to justify.
    vector<std::pair<Integer, ProofLine>> donor_rows;
    if (logger) {
        auto & tracker = logger->names_and_ids_tracker();

        inputs->before_flags.assign(n, {});
        inputs->after_flags.assign(n, {});
        inputs->active_flags.assign(n, {});
        inputs->contrib_flags.assign(n, {});
        inputs->ends.assign(n, std::nullopt);
        inputs->end_lines = make_shared<vector<std::optional<std::pair<ProofLine, ProofLine>>>>(n);

        for (auto i : inputs->active_tasks)
            for (Integer t = inputs->per_task_t_lo[i]; t <= per_task_t_hi[i]; ++t) {
                auto before = tracker.find_proof_flag_values(spec.donor, ConstraintProofModelData<Cumulative>::before_flag_key(i, t));
                auto after = tracker.find_proof_flag_values(spec.donor, ConstraintProofModelData<Cumulative>::after_flag_key(i, t));
                auto active = tracker.find_proof_flag_values(spec.donor, ConstraintProofModelData<Cumulative>::active_flag_key(i, t));
                // Missing means the donor never encoded this (task, time): it
                // was not installed, or it windowed the task differently. Either
                // way there is nothing to pin, so decline rather than guess.
                if (! before || ! after || ! active)
                    return false;
                inputs->before_flags[i].push_back(*before);
                inputs->after_flags[i].push_back(*after);
                inputs->active_flags[i].push_back(*active);
            }

        // One donor row per time point some task can occupy, which is exactly
        // where the donor wrote one.
        Integer global_lo = inputs->per_task_t_lo[inputs->active_tasks.front()], global_hi = per_task_t_hi[inputs->active_tasks.front()];
        for (auto i : inputs->active_tasks) {
            global_lo = std::min(global_lo, inputs->per_task_t_lo[i]);
            global_hi = std::max(global_hi, per_task_t_hi[i]);
        }

        for (Integer t = global_lo; t <= global_hi; ++t) {
            bool covered = false;
            for (auto i : inputs->active_tasks)
                if (t >= inputs->per_task_t_lo[i] && t <= per_task_t_hi[i]) {
                    covered = true;
                    break;
                }
            if (! covered)
                continue;

            auto row = tracker.constraint_row_label(spec.donor, ConstraintProofModelData<Cumulative>::capacity_row_role(t));
            if (! row)
                return false;
            donor_rows.emplace_back(t, *row);
        }
    }

    // Derive this constraint's own rows, here and now, at the top of the
    // proof: they must outlive every backtrack, since the propagator cites them
    // at every node. Nothing on this path reaches a ProofModel, so nothing here
    // can reach the OPB.
    //
    // Not through an install_initialiser, even though that is where a posted
    // constraint would do its once-only proof work: initialisers have already
    // run by the time a presolver is called (solve.cc runs them, then the
    // presolvers), so one installed from here would never fire and the
    // propagator would cite rows that were never written.
    if (logger) {
        logger->emit_proof_comment("derived cumulative: " + to_string(donor_rows.size()) + " capacity rows from " + as_string(spec.donor));
        for (const auto & [t, donor_row] : donor_rows)
            inputs->capacity_lines.emplace(t, spec.recipe(*logger, donor_row, t));
    }

    Triggers triggers;
    for (auto i : inputs->active_tasks)
        triggers.on_bounds.emplace_back(spec.starts[i]);

    propagators.install(
        inputs->owner,
        [inputs](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            return propagate_cumulative(*inputs, state, inference, logger);
        },
        triggers);

    return true;
}
