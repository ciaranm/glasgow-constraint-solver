#include <gcs/constraints/cumulative/derived_cumulative.hh>
#include <gcs/constraints/cumulative/hints.hh>
#include <gcs/constraints/cumulative/propagate.hh>
#include <gcs/constraints/innards/makespan_energy.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>

#include <algorithm>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_optional;
using std::make_shared;
using std::move;
using std::size_t;
using std::string;
using std::to_string;
using std::vector;

auto gcs::innards::derived_cumulative_tasks_from(const ConstraintID & donor, const vector<IntegerVariableID> & starts,
    const vector<Integer> & lengths, const vector<Integer> & heights, const vector<IntegerVariableID> & presences) -> vector<DerivedCumulativeTask>
{
    if (starts.size() != lengths.size() || starts.size() != heights.size())
        throw InvalidProblemDefinitionException{"derived Cumulative: starts, lengths, heights must have the same size"};
    if (! presences.empty() && starts.size() != presences.size())
        throw InvalidProblemDefinitionException{"derived Cumulative: starts and presences must have the same size"};

    vector<DerivedCumulativeTask> tasks;
    tasks.reserve(starts.size());
    for (size_t i = 0; i < starts.size(); ++i)
        tasks.push_back(
            DerivedCumulativeTask{donor, i, starts[i], lengths[i], heights[i], presences.empty() ? std::nullopt : make_optional(presences[i])});
    return tasks;
}

auto gcs::innards::install_derived_cumulative(
    Propagators & propagators, const State & initial_state, ProofLogger * const logger, DerivedCumulativeSpec spec) -> bool
{
    auto n = spec.tasks.size();
    if (spec.capacity < 0_i)
        throw InvalidProblemDefinitionException{"derived Cumulative: capacity must be non-negative"};
    for (const auto & task : spec.tasks)
        if (task.length < 0_i || task.height < 0_i)
            throw InvalidProblemDefinitionException{"derived Cumulative: lengths and heights must be non-negative"};
    if (! spec.recipe)
        throw InvalidProblemDefinitionException{"derived Cumulative: no recipe for deriving the capacity rows"};

    auto inputs = make_shared<CumulativeInputs>();
    inputs->owner = CurrentlyUnnamedConstraint{};
    inputs->capacity = constant_variable(spec.capacity);
    inputs->rules = spec.rules;

    // Each donor's own verdict on the task's presence, reached by the rule the
    // donor applied: the flags this constraint pins carry the literal that says
    // yes, so a reason of ours that left it out would be claiming a load the
    // task need not be carrying.
    vector<bool> never_present(n, false);
    inputs->presence.reserve(n);
    for (size_t i = 0; i < n; ++i) {
        auto resolved = cumulative_task_presence(spec.tasks[i].presence);
        inputs->presence.push_back(resolved.literal);
        never_present[i] = resolved.never_present;
    }

    for (const auto & task : spec.tasks) {
        inputs->starts.push_back(task.start);
        inputs->lengths.push_back(constant_variable(task.length));
        inputs->heights.push_back(constant_variable(task.height));
    }

    // The same windowing a posted Cumulative resolves in prepare(): a task can
    // be active from its earliest start to its latest finish, and one whose
    // length or height is zero, or which can never be present at all, never
    // raises the profile.
    inputs->per_task_t_lo.assign(n, 0_i);
    vector<Integer> per_task_t_hi(n, 0_i);
    for (size_t i = 0; i < n; ++i) {
        if (spec.tasks[i].length <= 0_i || spec.tasks[i].height <= 0_i || never_present[i])
            continue;
        inputs->active_tasks.push_back(i);
        auto [s_lo, s_hi] = initial_state.bounds(spec.tasks[i].start);
        inputs->per_task_t_lo[i] = s_lo;
        per_task_t_hi[i] = s_hi + spec.tasks[i].length - 1_i;
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

    // The donors' rows, to derive from. Resolved before anything is installed:
    // a derived constraint that cannot cite what it needs must not be installed
    // at all, since its propagator would then be drawing inferences it has no
    // way to justify.
    vector<std::pair<Integer, DerivedCumulativeRows>> rows_by_time;
    if (logger) {
        auto & tracker = logger->names_and_ids_tracker();

        inputs->before_flags.assign(n, {});
        inputs->after_flags.assign(n, {});
        inputs->active_flags.assign(n, {});
        inputs->contrib_flags.assign(n, {});
        inputs->ends.assign(n, std::nullopt);
        inputs->end_lines = make_shared<vector<std::optional<std::pair<ProofLine, ProofLine>>>>(n);

        for (auto i : inputs->active_tasks) {
            const auto & task = spec.tasks[i];
            auto position = task.position;
            for (Integer t = inputs->per_task_t_lo[i]; t <= per_task_t_hi[i]; ++t) {
                auto before = tracker.find_proof_flag_values(task.donor, ConstraintProofModelData<Cumulative>::before_flag_key(position, t));
                auto after = tracker.find_proof_flag_values(task.donor, ConstraintProofModelData<Cumulative>::after_flag_key(position, t));
                auto active = tracker.find_proof_flag_values(task.donor, ConstraintProofModelData<Cumulative>::active_flag_key(position, t));
                // Missing means that donor never encoded this (task, time): it
                // was not installed, or it windowed the task differently. Either
                // way there is nothing to pin, so decline rather than guess.
                if (! before || ! after || ! active)
                    return false;
                inputs->before_flags[i].push_back(*before);
                inputs->after_flags[i].push_back(*after);
                inputs->active_flags[i].push_back(*active);
            }
        }

        // One entry per time point some task of *this* constraint can occupy,
        // carrying whichever of the row donors wrote a row there. A donor with
        // nothing at that time is simply absent: the recipe is what knows
        // whether it needed it.
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

            DerivedCumulativeRows rows;
            for (const auto & donor : spec.row_donors)
                if (auto row = tracker.constraint_row_label(donor, ConstraintProofModelData<Cumulative>::capacity_row_role(t)))
                    rows.emplace(donor, *row);
            rows_by_time.emplace_back(t, move(rows));
        }
    }

    // Derive this constraint's own rows, here and now, at the top of the
    // proof: they must outlive every backtrack, since the propagator cites them
    // at every node. Nothing on this path reaches a ProofModel, so nothing here
    // can reach the OPB.
    //
    // Not through an install_initialiser, even though that is where a posted
    // constraint would do its once-only proof work. That used to be forced ---
    // initialisers had already run by the time a presolver was called, so one
    // installed from here never fired and the propagator cited rows that were
    // never written --- and #658 has since fixed the ordering. It stays inline
    // anyway, for a better reason: the caller is told whether this constraint
    // could be set up, and that answer has to be known now, while there is
    // still the option of not installing a propagator whose inferences could
    // not be justified.
    if (logger) {
        logger->emit_proof_comment(
            "derived cumulative: " + to_string(rows_by_time.size()) + " capacity rows over " + to_string(spec.row_donors.size()) + " donors");
        for (const auto & [t, rows] : rows_by_time) {
            auto derived = spec.recipe(*logger, rows, t);
            if (! derived)
                return false;
            inputs->capacity_lines.emplace(t, *derived);
        }
    }

    // The makespan bound, which is a statement about a variable this constraint
    // does not otherwise mention. It fires once, so it goes in an initialiser
    // rather than in the propagator: nothing it reads changes below the root
    // that would let it say more.
    if (spec.makespan) {
        // Which tasks can carry energy is the window-energy lemma's question,
        // and prepare_cumulative_overload_check is where it is answered. A
        // constraint posted for its energy alone runs with the overload rule
        // off, so ask anyway rather than going without a bound.
        if (! spec.rules.overload) {
            auto overload_data = prepare_cumulative_overload_check(
                inputs->starts, inputs->lengths, inputs->heights, inputs->active_tasks, inputs->per_task_t_lo, per_task_t_hi, initial_state);
            inputs->overload_tasks = move(overload_data.overload_tasks);
            inputs->time_slot_prefix = move(overload_data.time_slot_prefix);
            inputs->time_slot_lo = overload_data.time_slot_lo;
        }

        // Everything but the start bounds is settled now: the flag vectors live
        // in `inputs`, which the initialiser holds a share of, and the windows
        // are the ones its rows were derived over.
        vector<makespan_energy::EnergyTask> energy_tasks;
        vector<std::optional<IntegerVariableID>> energy_presences;
        for (auto i : inputs->overload_tasks) {
            energy_presences.push_back(inputs->presence[i]);
            energy_tasks.push_back(makespan_energy::EnergyTask{.start = std::get<SimpleIntegerVariableID>(spec.tasks[i].start),
                .length = spec.tasks[i].length,
                .height = spec.tasks[i].height,
                .t_lo = inputs->per_task_t_lo[i],
                .t_hi = per_task_t_hi[i],
                .start_lb = 0_i,
                .start_ub = 0_i,
                .link = i < spec.makespan_links.size() ? spec.makespan_links[i] : std::nullopt,
                .before = logger ? &inputs->before_flags[i] : nullptr,
                .after = logger ? &inputs->after_flags[i] : nullptr,
                .active = logger ? &inputs->active_flags[i] : nullptr});
        }

        propagators.install_initialiser(
            [inputs, energy_tasks, energy_presences, makespan = *spec.makespan, capacity = spec.capacity, mutation = spec.makespan_mutation,
                reached = spec.makespan_bound_reached](const State & state, auto & inference, ProofLogger * const logger) -> void {
                // An optional task's length x height is guaranteed work only
                // once it is known present, and at the root it usually is not.
                // Counting one that is undecided would claim energy the
                // schedule need not contain; leaving it out is a weaker bound
                // rather than a wrong one. Every task that is counted puts its
                // presence literal in the reason, which is what lets the
                // window-energy lemma's own presence terms go away.
                vector<makespan_energy::EnergyTask> counted;
                vector<IntegerVariableID> scope;
                ReasonLiterals presence_lits;
                for (size_t i = 0; i < energy_tasks.size(); ++i) {
                    if (energy_presences[i]) {
                        if (state.lower_bound(*energy_presences[i]) < 1_i)
                            continue;
                        presence_lits.push_back(*energy_presences[i] == 1_i);
                    }
                    auto & task = counted.emplace_back(energy_tasks[i]);
                    auto [s_lo, s_hi] = state.bounds(task.start);
                    task.start_lb = s_lo;
                    task.start_ub = s_hi;
                    scope.push_back(task.start);
                }

                if (counted.empty())
                    return;

                // What the model already says the makespan is, which an energy
                // argument has to beat to be worth making. The link rows give
                // it directly, and asking them is not the same as asking
                // `state`: initialisers run before anything has propagated, so
                // the makespan's own lower bound is still whatever it was
                // declared with. Without this the search below settles for a
                // window too narrow to hold every task --- which is sound, and
                // is a weaker number than the constraint deserves.
                auto [makespan_lo, makespan_hi] = state.bounds(makespan);
                auto known = makespan_lo;
                for (const auto & task : counted)
                    if (task.link)
                        known = std::max(known, task.start_lb + task.link->bound);

                auto bound =
                    makespan_energy::makespan_energy_bound(counted, capacity, inputs->time_slot_prefix, inputs->time_slot_lo, known, makespan_hi);
                if (! bound)
                    return;

                if (reached)
                    reached(bound->bound);

                // Tests only: claiming one more than the argument reaches must
                // be refused, since a derivation with slack in it verifies
                // whatever it concludes.
                auto claimed =
                    std::holds_alternative<makespan_energy::makespan_energy_mutation::ClaimHigherBound>(mutation) ? bound->bound + 1_i : bound->bound;

                auto justify = [&](const ReasonLiterals & reason) -> void {
                    if (logger)
                        makespan_energy::derive_makespan_bound(
                            *logger, reason, makespan, counted, inputs->capacity_lines, *bound, mutation, ProofLevel::Temporary);
                };

                inference.infer_greater_than_or_equal(logger, makespan, claimed,
                    JustifyExplicitly{justify, ThenRUP::Yes, hints::CumulativeMakespan{inputs->owner}},
                    with_extra(bounds_reason(scope), presence_lits));
            },
            InitialiserPriority::Expensive);
    }

    Triggers triggers;
    for (auto i : inputs->active_tasks)
        triggers.on_bounds.emplace_back(spec.tasks[i].start);

    propagators.install(
        inputs->owner,
        [inputs](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            return propagate_cumulative(*inputs, state, inference, logger);
        },
        triggers);

    return true;
}
