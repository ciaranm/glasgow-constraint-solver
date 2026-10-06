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
#include <functional>
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
    const vector<IntegerVariableID> & lengths, const vector<Integer> & heights, const vector<IntegerVariableID> & presences)
    -> vector<DerivedCumulativeTask>
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
        if (initial_state.lower_bound(task.length) < 0_i || task.height < 0_i)
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
        auto resolved = task_presence(spec.tasks[i].presence, "Cumulative");
        inputs->presence.push_back(resolved.literal);
        never_present[i] = resolved.never_present;
    }

    for (const auto & task : spec.tasks) {
        inputs->starts.push_back(task.start);
        inputs->lengths.push_back(task.length);
        inputs->heights.push_back(constant_variable(task.height));
    }

    // The same windowing a posted Cumulative resolves in prepare(), and by the
    // same function: only the same window finds the same flags, and a window
    // that disagreed would decline this constraint rather than fail loudly. A
    // task whose length or height can only be zero, or which can never be
    // present at all, never raises the profile and is not in it.
    inputs->per_task_t_lo.assign(n, 0_i);
    inputs->per_task_t_hi.assign(n, 0_i);
    auto & per_task_t_hi = inputs->per_task_t_hi;
    for (size_t i = 0; i < n; ++i) {
        if (initial_state.upper_bound(spec.tasks[i].length) <= 0_i || spec.tasks[i].height <= 0_i || never_present[i])
            continue;
        inputs->active_tasks.push_back(i);
        auto window = cumulative_task_window(initial_state, spec.tasks[i].start, spec.tasks[i].length);
        inputs->per_task_t_lo[i] = window.lo;
        per_task_t_hi[i] = window.hi;
    }

    if (inputs->active_tasks.empty())
        return false;

    // Also when the overload rule is off but a makespan was asked for: which
    // tasks can carry energy is the window-energy lemma's question either way,
    // and a constraint posted for its energy alone should not go without a
    // bound for want of asking.
    if (spec.rules.overload || spec.makespan) {
        auto overload_data = prepare_cumulative_overload_check(
            inputs->starts, inputs->lengths, inputs->heights, inputs->active_tasks, inputs->per_task_t_lo, per_task_t_hi, initial_state);
        inputs->overload_tasks = move(overload_data.overload_tasks);
        inputs->time_slot_prefix = move(overload_data.time_slot_prefix);
        inputs->time_slot_lo = overload_data.time_slot_lo;
    }

    // A derived Cumulative's own cache. Not the donor's: the rows are about
    // this constraint's window and this constraint's capacity lines, so sharing
    // one would have a firing cite a line derived against different rows.
    inputs->guarded_energy =
        make_shared<std::map<std::tuple<std::size_t, Integer, Integer, Integer, Integer, Integer>, window_energy::GuardedWindowEnergy>>();

    // Each task's flags are its donor's, keyed by its position there, and
    // asked for as they are cited (#1130): looked up here, per time point of
    // every window, they were named and defined over the whole horizon before
    // any rule had fired. Heights are constants by the time a task is built,
    // so no task has contribution bits.
    for (const auto & task : spec.tasks) {
        inputs->flag_owners.push_back(task.donor);
        inputs->flag_key_positions.push_back(task.position);
    }
    inputs->contribution_bit_counts.assign(n, 0);

    // Whether some task of this constraint can be running at `t`, which is
    // where it has a row. Captured by value, since the row deriver below
    // outlives this call.
    vector<CumulativeTaskWindow> windows;
    for (auto i : inputs->active_tasks)
        windows.push_back(CumulativeTaskWindow{inputs->per_task_t_lo[i], per_task_t_hi[i]});
    auto covered = [windows](Integer t) -> bool {
        return std::ranges::any_of(windows, [&](const CumulativeTaskWindow & w) { return t >= w.lo && t <= w.hi; });
    };

    // Everything below needs a logger, and a derived constraint that cannot
    // cite what it needs must not be installed at all, since its propagator
    // would then be drawing inferences it has no way to justify. So the checks
    // come before anything is installed.
    size_t rows_derived_here = 0;
    if (logger) {
        auto & tracker = logger->names_and_ids_tracker();
        inputs->end_ge_lines = make_shared<vector<std::optional<ProofLine>>>(n);

        for (auto i : inputs->active_tasks) {
            const auto & task = spec.tasks[i];
            auto position = task.position;

            // A task whose start and length both vary has its `after` reified
            // on the two-variable `start + length`, so pinning one goes through
            // the donor's proof-only end proxy --- and through the line giving
            // that proxy its lower bound, which is the donor's to publish and
            // ours only to cite. Missing means the donor derived none: it has a
            // constant somewhere after all, or the proof is being written with
            // assertions on, which omits definitions. Either way there is
            // nothing to pin `after` with, so decline rather than reach for a
            // RUP that cannot close.
            //
            // The bridge lemmas that make the pin land, `end >= t+1 -> after`,
            // need no such lookup: the donor emitted one at ProofLevel::Top for
            // every (i, t) it gave the task a window for, unit propagation
            // finds them, and the window check below establishes that this
            // constraint's window is inside that one.
            if (! is_constant_variable(task.start) && ! is_constant_variable(task.length)) {
                auto end_ge = tracker.find_derived_line(task.donor, ConstraintProofModelData<Cumulative>::end_lower_bound_role(position));
                if (! end_ge)
                    return false;
                (*inputs->end_ge_lines)[i] = *end_ge;
            }

            // The donor must have encoded this task over at least this
            // constraint's window: missing flags mean it was not installed, or
            // windowed the task differently, and either way there is nothing
            // to pin, so decline rather than guess. Asked at the window's two
            // ends only, because a donor's window is one unbroken run of time
            // points, so containing both ends is containing it all. This names
            // six flags, where asking at every point named the horizon.
            for (auto t : {inputs->per_task_t_lo[i], per_task_t_hi[i]})
                for (const auto & key : {ConstraintProofModelData<Cumulative>::before_flag_key(position, t),
                         ConstraintProofModelData<Cumulative>::after_flag_key(position, t),
                         ConstraintProofModelData<Cumulative>::active_flag_key(position, t)})
                    if (! tracker.find_proof_flag(task.donor, key))
                        return false;
        }

        // One attempt at the row for `t`: the donors' rows there, then the
        // recipe's derivation from them, which may decline.
        //
        // Each donor's own OPB row where it wrote one; failing that, ask the
        // donor's family to derive it (#780). Under
        // CumulativeEncoding::StartCheckpoint there is no `cap_<t>` label to
        // find, and the label lookup alone would come back empty, the recipe
        // would decline, and this whole constraint would go --- with no proof
        // failure to say so, since declining is a supported outcome here. The
        // label is tried first because where it exists it costs nothing, while
        // a derivation is `O(n^3)` lines. A published donor (#973) has only its
        // family, there being no posted Cumulative to have written a row. A
        // donor with nothing at `t` is simply absent: the recipe is what knows
        // whether it needed it.
        //
        // The recipe is moved into a share rather than copied into each
        // closure that holds it: a recipe's captures can be as big as the
        // horizon, and CumulativeStrengthening's are.
        auto attempt = [row_donors = spec.row_donors, recipe = make_shared<decltype(spec.recipe)>(move(spec.recipe))](
                           ProofLogger & row_logger, Integer t) -> std::optional<ProofLine> {
            auto & row_tracker = row_logger.names_and_ids_tracker();
            DerivedCumulativeRows rows;
            for (const auto & donor : row_donors) {
                auto posted = donor.row_family == ConstraintProofModelData<Cumulative>::capacity_row_family();
                if (auto row = posted ? row_tracker.constraint_row_label(donor.id, ConstraintProofModelData<Cumulative>::capacity_row_role(t))
                                      : std::nullopt)
                    rows.emplace(donor, *row);
                else if (auto derived = row_tracker.find_or_derive_line_in_family(donor.id, donor.row_family, t, row_logger))
                    rows.emplace(donor, *derived);
            }
            return (*recipe)(row_logger, rows, t);
        };

        // Where the recipe's answer can change: wherever a window of this
        // constraint's tasks starts or ends. Between two of these the same
        // tasks have flags, and a recipe's answer depends on nothing else (see
        // DerivedCumulativeSpec::recipe), so asking at the first point of each
        // stretch is asking about all of it.
        vector<Integer> edges;
        for (const auto & w : windows) {
            edges.push_back(w.lo);
            edges.push_back(w.hi + 1_i);
        }
        std::ranges::sort(edges);
        edges.erase(std::unique(edges.begin(), edges.end()), edges.end());

        // Asked here and now, at the top of the proof, so that a decline is
        // known while there is still the option of not installing a
        // propagator whose inferences could not be justified. What each
        // attempt derives is a row like any other, and stays for the
        // propagator to cite.
        inputs->lazy_capacity_rows = make_shared<LazyCapacityRows>();
        for (auto t : edges) {
            if (! covered(t))
                continue;
            auto derived = attempt(*logger, t);
            if (! derived) {
                // The rows for the earlier stretches are already at Top, and
                // nothing will ever cite them: this constraint is not being
                // installed, so its propagator does not exist. Top is never
                // forgotten, so leaving them there is #666 again --- live
                // constraints for the rest of the proof, taxing every later
                // unhinted RUP --- on the decline path this time rather than
                // the success one. A recipe declining is not an error and not
                // rare: a cut spanning several donors reaches time points one
                // of them wrote no row for.
                //
                // Only the declining *return* is cleaned up like this. A recipe
                // that throws leaves its orphans behind, and deliberately: an
                // exception out of here means the run is over, so there is no
                // later proof for them to tax. The decline fixture does not
                // cover that path, and nothing else does either.
                vector<ProofLine> orphans;
                for (const auto & [_, line] : inputs->lazy_capacity_rows->derived)
                    orphans.push_back(*line);
                if (! orphans.empty()) {
                    logger->emit_proof_comment("derived cumulative: declined at time " + to_string(t.raw_value) + ", dropping " +
                        to_string(orphans.size()) + " rows already derived");
                    logger->delete_proof_lines(orphans);
                }
                return false;
            }
            inputs->lazy_capacity_rows->derived.emplace(t, derived);
            ++rows_derived_here;
        }

        // Every other row, the first time something cites it. Not through an
        // install_initialiser or a published family: a derived constraint has
        // no ConstraintID of its own to publish one under, and the rows are
        // needed wherever its propagator is, not once at the root. Nothing on
        // this path reaches a ProofModel, so nothing here can reach the OPB.
        inputs->lazy_capacity_rows->derive = [attempt, covered, stats = spec.stats](ProofLogger & row_logger, Integer t) -> std::optional<ProofLine> {
            if (! covered(t))
                return std::nullopt;
            auto derived = attempt(row_logger, t);
            if (! derived)
                throw UnexpectedException{"derived Cumulative: the recipe declined at time " + to_string(t.raw_value) +
                    ", having derived a row where the same windows cover the same tasks; a recipe's answer may depend on the time only through "
                    "which windows cover it"};
            if (stats)
                ++stats->capacity_rows;
            return derived;
        };
    }

    // The makespan bound, which is a statement about a variable this constraint
    // does not otherwise mention. It fires once, so it goes in an initialiser
    // rather than in the propagator: nothing it reads changes below the root
    // that would let it say more.
    if (spec.makespan) {
        // Everything but the start bounds is settled now: the flags are read
        // through `inputs`, which the initialiser holds a share of, and the
        // windows are the ones its rows are derived over. Through accessors,
        // which ask for a flag's definition before citing it and name no more
        // flags than the window-energy lemma cites.
        auto flag_accessor = [inputs, logger](size_t i, CumulativeFlag which)->std::function<auto(size_t) -> ProofFlag> {
            if (! logger)
                return {};
            return [inputs, logger, i, which](size_t idx) -> ProofFlag {
                auto t = inputs->per_task_t_lo[i] + Integer{static_cast<long long>(idx)};
                ensure_cumulative_flags_defined(*inputs, *logger, i, t);
                return cumulative_flag(*inputs, logger->names_and_ids_tracker(), which, i, t);
            };
        };
        vector<makespan_energy::EnergyTask> energy_tasks;
        vector<std::optional<IntegerVariableID>> energy_presences;
        for (auto i : inputs->overload_tasks) {
            // A plain variable and a constant. The start is by construction ---
            // prepare_cumulative_overload_check keeps only such tasks --- but
            // the length is not: that filter admits a variable one and counts it
            // at the duration it guarantees (#689), which the makespan bound
            // cannot do, its rows being built once at the root off a length that
            // has to be a number. So a variable-duration task takes part in the
            // time-tabling, in the rows and in the overload check's energy, and
            // stays out of the makespan argument alone.
            //
            // Checked rather than assumed, because the invariant lives in
            // another file: what would arrive here otherwise is a
            // std::bad_variant_access from inside an install initialiser, and
            // what should arrive is nothing at all.
            if (! std::holds_alternative<SimpleIntegerVariableID>(spec.tasks[i].start) || ! is_constant_variable(spec.tasks[i].length))
                continue;

            energy_presences.push_back(inputs->presence[i]);
            energy_tasks.push_back(makespan_energy::EnergyTask{.start = std::get<SimpleIntegerVariableID>(spec.tasks[i].start),
                .length = constant_value_of(spec.tasks[i].length),
                .height = spec.tasks[i].height,
                .t_lo = inputs->per_task_t_lo[i],
                .t_hi = per_task_t_hi[i],
                .start_lb = 0_i,
                .start_ub = 0_i,
                .link = i < spec.makespan_links.size() ? spec.makespan_links[i] : std::nullopt,
                .flag_count = static_cast<size_t>(std::max(0LL, (per_task_t_hi[i] - inputs->per_task_t_lo[i] + 1_i).raw_value)),
                .before = flag_accessor(i, CumulativeFlag::Before),
                .after = flag_accessor(i, CumulativeFlag::After),
                .active = flag_accessor(i, CumulativeFlag::Active)});
        }

        propagators.install_initialiser(
            [inputs, energy_tasks, energy_presences, makespan = *spec.makespan, capacity = spec.capacity, mutation = spec.makespan_mutation,
                reached = spec.makespan_bound_reached, not_improving = spec.makespan_bound_not_improving,
                rows_lo = std::ranges::min(windows, {}, &CumulativeTaskWindow::lo).lo,
                derived_stats = spec.stats](const State & state, auto & inference, ProofLogger * const logger) -> void {
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
                if (! bound) {
                    if (not_improving)
                        not_improving();
                    return;
                }

                if (reached)
                    reached(bound->bound);

                if (derived_stats)
                    ++derived_stats->makespan_bounds_posted;

                // Tests only: claiming one more than the argument reaches must
                // be refused, since a derivation with slack in it verifies
                // whatever it concludes.
                auto claimed =
                    std::holds_alternative<makespan_energy::makespan_energy_mutation::ClaimHigherBound>(mutation) ? bound->bound + 1_i : bound->bound;

                auto justify = [&](const ReasonLiterals & reason) -> void {
                    if (! logger)
                        return;
                    // The rows the derivation sums: every one this constraint
                    // has below the window's end, which is what it summed when
                    // they were all derived up front. One further under
                    // ClaimHigherBound, whose corrupted window may reach it.
                    auto rows_end =
                        std::holds_alternative<makespan_energy::makespan_energy_mutation::ClaimHigherBound>(mutation) ? bound->hi + 1_i : bound->hi;
                    std::map<Integer, ProofLine> rows;
                    for (Integer t = rows_lo; t < rows_end; ++t)
                        if (auto row = inputs->lazy_capacity_rows->row(*logger, t))
                            rows.emplace(t, *row);
                    makespan_energy::derive_makespan_bound(*logger, reason, makespan, counted, rows, *bound, mutation, ProofLevel::Temporary);
                };

                inference.infer_greater_than_or_equal(logger, makespan, claimed,
                    JustifyExplicitly{justify, ThenRUP::Yes, hints::CumulativeMakespan{inputs->owner}},
                    with_extra(bounds_reason(scope), presence_lits));
            },
            InitialiserPriority::Expensive);
    }

    // The same trigger set a posted Cumulative installs, minus the two a
    // derived one cannot have: its capacity is an Integer and its heights are
    // Integers by the time a task is built, so neither can move. Lengths and
    // presences can, and the arguments for waking on them are the posted
    // constraint's verbatim --- a rise in a length's lower bound extends a
    // mandatory part, and a presence fixed to 1 puts a task into the load
    // profile. Missing them costs the derived constraint pruning it is entitled
    // to, silently and with no test able to see it, since late is still sound.
    Triggers triggers;
    for (auto i : inputs->active_tasks)
        triggers.on_bounds.emplace_back(spec.tasks[i].start);
    for (auto i : inputs->active_tasks)
        if (! is_constant_variable(spec.tasks[i].length))
            triggers.on_bounds.emplace_back(spec.tasks[i].length);
    for (auto i : inputs->active_tasks)
        if (inputs->presence[i] && ! is_constant_variable(*inputs->presence[i]))
            triggers.on_instantiated.emplace_back(*inputs->presence[i]);

    propagators.install(
        inputs->owner,
        [inputs](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            return propagate_cumulative(*inputs, state, inference, logger);
        },
        triggers);

    // Only here, on the success path: every decline above returns without
    // installing anything, and a block saying a constraint was derived when it
    // was not is worse than one saying nothing. The caller's aggregate, not a
    // component of this constraint's own --- see DerivedCumulativeSpec::stats.
    if (spec.stats) {
        ++spec.stats->constraints;
        spec.stats->donors += spec.row_donors.size();
        spec.stats->capacity_rows += rows_derived_here;
    }

    return true;
}
