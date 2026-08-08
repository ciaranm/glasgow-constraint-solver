#include <gcs/constraint_id.hh>
#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/cumulative/derived_cumulative.hh>
#include <gcs/constraints/cumulative/donor_view.hh>
#include <gcs/constraints/cumulative/propagate.hh>
#include <gcs/exception.hh>
#include <gcs/innards/proofs/am1_from_row.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_scaffolding_scope.hh>
#include <gcs/innards/proofs/subset_sum_strengthening.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>
#include <gcs/presolvers/cumulative_strengthening/cumulative_strengthening.hh>
#include <gcs/problem.hh>
#include <util/overloaded.hh>

#include <algorithm>
#include <map>
#include <memory>
#include <numeric>
#include <optional>
#include <string>
#include <utility>
#include <variant>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_optional;
using std::make_shared;
using std::make_unique;
using std::map;
using std::max;
using std::min;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::shared_ptr;
using std::size_t;
using std::string;
using std::to_string;
using std::unique_ptr;
using std::vector;
using std::ranges::all_of;
using std::ranges::any_of;
using std::ranges::max_element;
using std::ranges::sort;

namespace
{
    /// What the presolver worked out for one time point: the tasks that can be
    /// running then, split into the ones that fill the resource on their own
    /// and the ones that do not, and the largest load the latter can actually
    /// reach without exceeding the capacity.
    struct TimePoint
    {
        Integer t;
        vector<size_t> tasks;
        vector<Integer> heights;
        vector<size_t> full_tasks;
        Integer kappa;
        /// Whether derive_subset_sum_strengthening() will take its two-step
        /// divisibility path here, predicted by the same test it applies. Only
        /// the other path costs anything worth budgeting for.
        bool by_division;
    };

    /// The step sizes that raise one task's coefficient from zero to `kappa`,
    /// in a row whose other coefficients total `total` and whose right hand
    /// side is `kappa` --- one `pol` each.
    ///
    /// Each step is `lambda` copies of the row so far plus the at-most-ones
    /// tying the task to the row's other terms, weighted by those terms' own
    /// coefficients, all divided by `lambda + e`. Working out the largest step
    /// that division survives is the whole of this: the division rounds the
    /// degree *up*, and the margin it has to round through is `e * (total -
    /// kappa)`, so a step of `k` lands on the right hand side again exactly
    /// when `k * (total - kappa) < total - c`. That bound is what is being
    /// computed here, one step at a time.
    ///
    /// So the cost is not uniform. A row whose other tasks only just overshoot
    /// the capacity raises in a single step; one that overshoots by half gets
    /// steps of one and pays a `pol` per unit of `kappa`, which is why the
    /// caller budgets this. Predicting it is arithmetic and needs no proof, so
    /// the budget and the derivation walk the same steps --- a prediction that
    /// disagreed would decline the wrong donors.
    template <typename Step_>
    auto for_each_raise_step(Integer total, Integer kappa, Step_ && each_step) -> void
    {
        // Everything else fits alongside, so the at-most-ones alone say it:
        // summed, they give the whole row in one `pol`, and there is no
        // division to survive.
        if (total <= kappa) {
            each_step(kappa);
            return;
        }

        auto overshoot = total - kappa;
        for (auto c = 0_i; c < kappa;) {
            // ceil((total - c) / overshoot) - 1, which is at least one while
            // `c < kappa`, so this terminates.
            auto step = min(kappa - c, (total - c + overshoot - 1_i) / overshoot - 1_i);
            each_step(step);
            c += step;
        }
    }

    /// \ref for_each_raise_step, as the steps themselves.
    [[nodiscard]] auto raise_steps(Integer total, Integer kappa) -> vector<Integer>
    {
        vector<Integer> steps;
        for_each_raise_step(total, kappa, [&](Integer step) { steps.push_back(step); });
        return steps;
    }

    /// \ref for_each_raise_step, as how many there are --- which is all the
    /// budget wants, and it wants it once per raised task per time point, on
    /// the path whose whole purpose is to decide cheaply whether the expensive
    /// one is affordable.
    [[nodiscard]] auto raise_step_count(Integer total, Integer kappa) -> long long
    {
        long long count = 0;
        for_each_raise_step(total, kappa, [&](Integer) { ++count; });
        return count;
    }
}

CumulativeStrengthening::CumulativeStrengthening(shared_ptr<CumulativeStrengtheningStats> stats) :
    // Always a block, whether or not anyone asked for one: the default
    // experience was silent because nothing was allocated, not because the
    // channel was wrong.
    _stats(stats ? move(stats) : make_shared<CumulativeStrengtheningStats>()), _max_dynamic_programming_states(20000), _max_raise_lines(5000),
    _max_subset_sum_capacity(1000000),
    // Energy rules only: see with_rules(). A derived constraint's time-tabling
    // cannot infer anything its donor's has not, so running it is pure cost.
    _rules(CumulativeRules{.time_table = false, .overload = true, .profile_overload = true}), _mutation(cumulative_strengthening_mutation::None{})
{
}

auto CumulativeStrengthening::with_dynamic_programming_budget(long long states) -> CumulativeStrengthening &
{
    _max_dynamic_programming_states = states;
    return *this;
}

auto CumulativeStrengthening::with_raise_budget(long long lines) -> CumulativeStrengthening &
{
    _max_raise_lines = lines;
    return *this;
}

auto CumulativeStrengthening::with_subset_sum_capacity_limit(long long capacity) -> CumulativeStrengthening &
{
    _max_subset_sum_capacity = capacity;
    return *this;
}

auto CumulativeStrengthening::with_rules(CumulativeRules rules) -> CumulativeStrengthening &
{
    _rules = rules;
    return *this;
}

auto CumulativeStrengthening::with_proof_mutation(CumulativeStrengtheningMutation mutation) -> CumulativeStrengthening &
{
    _mutation = mutation;
    return *this;
}

auto CumulativeStrengthening::run(Problem & problem, Propagators & propagators, State & state, ProofLogger * const logger) -> bool
{
    // Before the loop, and unconditionally: a presolver that found nothing to
    // look at is the case worth being able to see, and it is the one every
    // other check passes without noticing.
    propagators.add_component_stats(_stats);

    auto bump = [&](size_t CumulativeStrengtheningStats::* field) { ++((*_stats).*field); };

    auto note = [&](StatsLevel level, optional<ConstraintID> constraint, string text) {
        propagators.report(StatsNote{.level = level, .component = _stats->component_name(), .constraint = move(constraint), .text = move(text)});
    };

    // This run's own tally, rather than the block's: a block shared across two
    // solves would otherwise have the first solve's declines counted into the
    // second's summary note.
    auto donors_before = _stats->donors_seen;
    size_t limit_declines_this_run = 0;

    for (const auto & donor : problem.each_constraint_of_type<Cumulative>()) {
        bump(&CumulativeStrengtheningStats::donors_seen);

        // Everything below is an argument about the donor's per-time rows
        // `Σ h_i·active_{i,t} ≤ C`, which only says that when every argument is
        // a constant --- so this is where a donor that is not all constants
        // gets reduced to the part of itself that is. The reduction is per
        // *task*: one variable height no longer costs a whole donor its
        // strengthening, it costs that task its term. A variable length costs
        // nothing at all --- no length is in a row --- so long as the donor
        // published what a pin of that task's `after` needs. Optional tasks need
        // nothing at all, their presence being a conjunct inside the activity
        // flag rather than a term beside it.
        auto view = cumulative_donor_view(donor, state, logger);
        if (! view) {
            bump(&CumulativeStrengtheningStats::declined_irreducible_capacity);
            note(StatsLevel::General, donor.constraint_id(),
                "passed over: its capacity is a view, which cannot be reduced to a number to strengthen against");
            continue;
        }
        const auto & starts = donor.starts();
        auto n = starts.size();
        auto capacity = view->capacity;
        auto unentitled_raise = std::holds_alternative<cumulative_strengthening_mutation::RaiseUnentitled>(_mutation);

        // The assessment below subset-sums the heights at every time point, and
        // that is a bitset of `capacity` bits built from scratch each time. It
        // runs before any of the proof budgets, and with proofs off none of
        // them ever runs at all --- so a donor posted in scaled units, with a
        // capacity in the billions, spends hundreds of megabytes and a sweep of
        // the whole horizon before anything has decided whether there was a
        // strengthening to be had. Magnitude is the wrong thing to find that
        // out with, so decline on it first. It is also what keeps the state
        // count and the raise arithmetic below inside a `long long`.
        if (capacity > Integer{_max_subset_sum_capacity}) {
            bump(&CumulativeStrengtheningStats::declined_capacity_too_large);
            ++limit_declines_this_run;
            note(StatsLevel::General, donor.constraint_id(),
                "passed over: its capacity of " + to_string(capacity.raw_value) + " is beyond the subset-sum limit of " +
                    to_string(_max_subset_sum_capacity) + ", see with_subset_sum_capacity_limit");
            continue;
        }

        // A task whose *guaranteed* demand is above the capacity means the
        // donor is infeasible on its own, which is the donor's business to
        // detect and not something to build a subset sum over. Asked here
        // rather than inside the assessment, and counted on its own: setting
        // such a task aside takes its height to zero and hides the
        // infeasibility, so an assessment of the set-aside candidate would go
        // on to strengthen around it and report an ordinary decline --- and
        // this stats block exists precisely because a presolver doing nothing
        // passes every other check.
        if (any_of(view->usable, [&](size_t i) { return view->heights[i] > capacity; })) {
            bump(&CumulativeStrengtheningStats::declined_infeasible_donor);
            note(StatsLevel::General, donor.constraint_id(),
                "passed over: a task's guaranteed demand is greater than the capacity, so the constraint is infeasible on its own");
            continue;
        }

        // Everything about a candidate view that decides whether it is worth
        // strengthening over, and what the strengthening would be. A candidate
        // rather than *the* view, because a donor with a variable height has
        // two: one that converts such a task into its guaranteed demand and one
        // that sets it aside. Nullopt means this candidate has nothing to say.
        struct Assessment
        {
            vector<size_t> full_tasks;
            vector<TimePoint> time_points;
            Integer kappa = 0_i;
        };

        auto assess = [&](const CumulativeDonorView & candidate) -> optional<Assessment> {
            const auto & active_tasks = candidate.usable;
            if (active_tasks.empty())
                return nullopt;

            // The same windowing install_derived_cumulative resolves, and by
            // the same function: this is the paper's `t in [est_j, lct_j)`, and
            // a window disagreeing with the donor's would simply find no flags.
            // Local to the assessment: what comes out of it is the time points,
            // which is where the windows have already been applied, so nothing
            // downstream asks about them again.
            Assessment assessment;
            vector<Integer> t_lo(n, 0_i), t_hi(n, 0_i);
            for (auto i : active_tasks) {
                auto window = cumulative_task_window(state, starts[i], candidate.lengths[i]);
                t_lo[i] = window.lo;
                t_hi[i] = window.hi;
            }

            // Schulz's coefficient raising, as the set of tasks it applies to.
            // A task that cannot run beside any *other* task that consumes
            // anything occupies the resource whenever it runs, whatever its
            // height says, so its height is really the capacity --- and, once
            // the capacity comes down to kappa below, really kappa.
            //
            // Stated as the pairwise test rather than as the paper's
            // `c_i > C - min_j c_j`, because the two are the same condition and
            // the pairwise one is what the certificate needs anyway: it is one
            // at-most-one per pair, each derived from the donor's own row.
            // Tasks whose windows cannot overlap are not part of it, which is a
            // little more than the paper claims and costs nothing --- if they
            // can never be active together, no row ever mentions both.
            //
            // Deliberately *not* per time point, even though fewer tasks can
            // run at one time point than over the whole horizon and the set
            // would be larger for it: a Cumulative has one height per task, not
            // one per time point, so a task that only fills the resource at
            // some of them cannot be given a raised height at all.
            //
            // A *loner* --- a task whose window overlaps nobody's --- comes out
            // full vacuously. That is correct as far as it goes, and it costs
            // something: with every task a loner, `other_tasks` is empty, kappa
            // is zero and the donor is declined, where plain subset-summing
            // over all of them would have strengthened it. Rare enough to be
            // written down rather than special-cased, and if scheduling
            // competitiveness ever cares the answer is that a loner is an
            // ordinary task, not a full one. See also #702, which is the other
            // thing this presolver leaves on the table.
            auto & full_tasks = assessment.full_tasks;
            vector<size_t> other_tasks;
            for (auto i : active_tasks) {
                auto conflicts_with_everything = all_of(active_tasks, [&](size_t j) {
                    return i == j || t_hi[i] < t_lo[j] || t_hi[j] < t_lo[i] || candidate.heights[i] + candidate.heights[j] > capacity;
                });
                (conflicts_with_everything ? full_tasks : other_tasks).push_back(i);
            }

            // The mutation that says the pairwise test is the load-bearing
            // part: take the tallest task that did *not* qualify and raise it
            // anyway. Everything downstream then runs honestly on a set that is
            // wrong, and the row it lands on is a row the donor does not imply.
            if (unentitled_raise && ! other_tasks.empty()) {
                auto tallest = max_element(other_tasks, [&](size_t a, size_t b) { return candidate.heights[a] < candidate.heights[b]; });
                full_tasks.push_back(*tallest);
                other_tasks.erase(tallest);
                sort(full_tasks);
            }

            auto global_lo = t_lo[active_tasks.front()], global_hi = t_hi[active_tasks.front()];
            for (auto i : active_tasks) {
                global_lo = min(global_lo, t_lo[i]);
                global_hi = max(global_hi, t_hi[i]);
            }

            for (Integer t = global_lo; t <= global_hi; ++t) {
                TimePoint point{t, {}, {}, {}, 0_i, false};
                for (auto i : other_tasks)
                    if (t >= t_lo[i] && t <= t_hi[i]) {
                        point.tasks.push_back(i);
                        point.heights.push_back(candidate.heights[i]);
                    }
                for (auto i : full_tasks)
                    if (t >= t_lo[i] && t <= t_hi[i])
                        point.full_tasks.push_back(i);

                // No task can be active here, so the donor wrote no row and
                // there is nothing to derive from.
                if (point.tasks.empty() && point.full_tasks.empty())
                    continue;

                point.kappa = largest_subset_sum_at_most(point.heights, capacity);

                auto divisor = 0_i;
                for (const auto & h : point.heights)
                    divisor = Integer{std::gcd(divisor.raw_value, h.raw_value)};
                point.by_division = (divisor > 1_i && divisor * (capacity / divisor) == point.kappa);

                assessment.kappa = max(assessment.kappa, point.kappa);
                assessment.time_points.push_back(move(point));
            }

            // Every task fills the resource on its own, so the tasks the
            // capacity is a subset sum *of* are none of them and kappa is zero.
            // That is not a strengthening but a disjunctive, and inferring
            // those from conflict cliques is what the InferredDisjunctive
            // presolver does.
            if (assessment.kappa <= 0_i)
                return nullopt;

            // kappa is the largest load reachable at any one time point once
            // the tasks that fill the resource are set aside, so it is what the
            // capacity really is. If that is the capacity already, and no
            // task's height changes either, the donor was posted with the
            // numbers it deserved and there is nothing here.
            auto raises_a_height = any_of(full_tasks, [&](size_t i) { return candidate.heights[i] != assessment.kappa; });
            if (assessment.kappa >= capacity && ! raises_a_height)
                return nullopt;

            return assessment;
        };

        auto assessed = assess(*view);

        // Converting a variable height is not free. kappa is the largest subset
        // sum of the heights the capacity allows, so *adding* a task can only
        // push it up, and a converted task can therefore cost this donor the
        // very reduction the presolver exists to make: heights {3, 3} under a
        // capacity of eight give six, and converting a task at a guaranteed
        // demand of two gives {3, 3, 2}, whose largest subset sum at most eight
        // is eight --- no strengthening at all where there used to be two units
        // of one. Against that, the converted task's energy joins the derived
        // constraint's overload check, which is the only rule it runs.
        //
        // Neither direction dominates and both are arithmetic, so work out both
        // and keep the bigger reduction rather than assuming. A tie goes to the
        // converted one, which says the same about the capacity over more tasks.
        if (any_of(view->height_bounded_by, [](const auto & h) { return h.has_value(); })) {
            auto without = view->with_converted_heights_set_aside();
            if (auto set_aside_instead = assess(without); set_aside_instead && (! assessed || set_aside_instead->kappa < assessed->kappa)) {
                bump(&CumulativeStrengtheningStats::donors_better_off_setting_heights_aside);
                assessed = move(set_aside_instead);
                *view = move(without);
            }
        }

        if (! assessed) {
            bump(&CumulativeStrengtheningStats::declined_nothing_to_gain);
            note(StatsLevel::Detailed, donor.constraint_id(),
                "passed over: its capacity is already the largest load its tasks can reach, and no height moved either");
            continue;
        }

        // Counted from the view that was actually used, since the choice above
        // can turn a converted task back into a set-aside one.
        if (! view->set_aside.empty())
            bump(&CumulativeStrengtheningStats::donors_with_set_aside_tasks);
        for (auto i : view->usable)
            if (view->height_bounded_by[i])
                bump(&CumulativeStrengtheningStats::converted_heights);

        const auto & full_tasks = assessed->full_tasks;
        auto & time_points = assessed->time_points;
        auto kappa = assessed->kappa;

        // Budget the expensive derivations. The dynamic program has a state per
        // reachable partial sum per item, so `items * capacity` bounds it; the
        // divisibility path is two `pol` steps and needs no budgeting. Raising
        // is a `pol` per step per task per time point, and how many steps a
        // raise takes depends on how far the rest of the row overshoots. Only
        // relevant with proofs on, since with them off no derivation happens.
        if (logger) {
            long long states = 0, raise_lines = 0;
            for (const auto & point : time_points) {
                if (! point.by_division)
                    states += static_cast<long long>(point.heights.size()) * (capacity.raw_value + 1);

                // A repeat count rather than an index: each raised task is
                // raised out of the row the one before it left behind, which is
                // a kappa heavier, so what varies between the rounds is `total`
                // and not which task it is.
                auto total = std::accumulate(point.heights.begin(), point.heights.end(), 0_i);
                for (size_t rounds = point.full_tasks.size(); rounds > 0; --rounds) {
                    raise_lines += raise_step_count(total, kappa);
                    total += kappa;
                }
            }

            if (states > _max_dynamic_programming_states) {
                bump(&CumulativeStrengtheningStats::declined_over_budget);
                ++limit_declines_this_run;
                note(StatsLevel::General, donor.constraint_id(),
                    "passed over: the derivation would need " + to_string(states) + " dynamic programming states against a budget of " +
                        to_string(_max_dynamic_programming_states) + ", see with_dynamic_programming_budget");
                continue;
            }

            if (raise_lines > _max_raise_lines) {
                bump(&CumulativeStrengtheningStats::declined_over_raise_budget);
                ++limit_declines_this_run;
                note(StatsLevel::General, donor.constraint_id(),
                    "passed over: raising heights would need " + to_string(raise_lines) + " proof lines against a budget of " +
                        to_string(_max_raise_lines) + ", see with_raise_budget");
                continue;
            }
        }

        // The recipe needs to find, for each time point, the same tasks and the
        // same flags that the donor's row for that time point is over --- so
        // that the subset sum it strengthens is a subset sum of exactly that
        // row's coefficients. By value: the recipe is called before this
        // iteration ends today, but a capture that only works because of that
        // is one refactor away from being a use-after-free nobody sees.
        map<Integer, TimePoint> by_time;
        for (auto & point : time_points)
            by_time.emplace(point.t, move(point));

        auto donor_id = donor.constraint_id();
        auto heights = view->heights;
        auto stats = _stats;

        // The raised tasks occupy the whole of the strengthened resource, which
        // is what the raising rule says once the capacity is kappa.
        auto derived_heights = heights;
        for (auto i : full_tasks)
            derived_heights[i] = kappa;

        // Fixed for the whole donor, so worked out once rather than per row.
        SubsetSumMutation subset_sum_corruption = overloaded{//
            [](const cumulative_strengthening_mutation::ClaimOneBetter &) -> SubsetSumMutation { return subset_sum_mutation::ClaimOneBetter{}; },
            [](const cumulative_strengthening_mutation::BogusDivisor &) -> SubsetSumMutation { return subset_sum_mutation::BogusDivisor{}; },
            [](const auto &) -> SubsetSumMutation {
                return subset_sum_mutation::None{};
            }}.visit(_mutation);
        auto raise_too_fast = std::holds_alternative<cumulative_strengthening_mutation::RaiseTooFast>(_mutation);

        DerivedCumulativeSpec spec{.tasks = derived_cumulative_tasks_from(donor_id, starts, view->lengths, derived_heights, view->presences),
            .capacity = kappa,
            .row_donors = {donor_id},
            .recipe = [donor_id, view = *view, heights, capacity, kappa, by_time, stats, subset_sum_corruption, raise_too_fast, unentitled_raise](
                          ProofLogger & recipe_logger, const DerivedCumulativeRows & rows, Integer t) -> optional<ProofLine> {
                auto point = by_time.find(t);
                if (point == by_time.end())
                    throw ProofError{"cumulative strengthening: no time point worked out for " + to_string(t.raw_value)};

                // The donor is the only row source, and it wrote a row wherever
                // this constraint has one, since they cover the same tasks.
                auto donor_row_at = rows.find(donor_id);
                if (donor_row_at == rows.end())
                    throw ProofError{"cumulative strengthening: the donor has no capacity row at time " + to_string(t.raw_value) +
                        ", which cannot happen for a constraint derived over all of its tasks"};

                auto & tracker = recipe_logger.names_and_ids_tracker();
                auto flag_for = [&](size_t i) -> ProofFlag {
                    auto active = tracker.find_proof_flag_values(donor_id, ConstraintProofModelData<Cumulative>::active_flag_key(i, t));
                    if (! active)
                        throw ProofError{"cumulative strengthening: the donor has no active flag for task " + to_string(i) + " at time " +
                            to_string(t.raw_value) + ", which install_derived_cumulative should already have declined over"};
                    return *active;
                };

                const auto & full_here = point->second.full_tasks;

                vector<SubsetSumItem> items;
                for (auto i : point->second.tasks)
                    items.push_back(SubsetSumItem{heights[i], flag_for(i)});

                // What the derived constraint was declared to say here, which
                // every path below closes by pinning.
                WPBSum load;
                for (auto i : full_here)
                    load += kappa * flag_for(i);
                for (const auto & item : items)
                    load += item.coefficient * std::get<ProofFlag>(item.term);

                // Everything between here and the pin is working: the
                // strengthened rows, the at-most-ones and the raises all exist
                // only to reach the line this returns, and at Top not one of
                // them would ever be deleted (issue #666, which is the same
                // defect one presolver over). One level deeper, and forgotten
                // on the way out.
                ProofScaffoldingScope scaffolding{recipe_logger};

                // The row everything below argues from, reduced to the
                // constant-argument form it reads it as: the set-aside tasks'
                // terms weakened away, and a variable capacity replaced by the
                // number `capacity` already holds. Working like the rest, so it
                // goes inside the level that gets forgotten.
                auto reduced_row = recover_constant_argument_row(recipe_logger, view, donor_id, donor_row_at->second, t, ProofLevel::Temporary);
                if (! reduced_row)
                    return std::nullopt;
                auto donor_row = *reduced_row;

                auto strengthen_to_kappa = [&](ProofLine source) -> ProofLine {
                    auto strengthened =
                        derive_subset_sum_strengthening(recipe_logger, items, source, capacity, ProofLevel::Temporary, subset_sum_corruption);
                    // After the call rather than before it, and off what came
                    // back rather than off the assessment's prediction: the
                    // marker and the counter then agree with each other and
                    // with the line, where predicting has them disagree on
                    // every point the arithmetic settles differently.
                    //
                    // A line that came back unchanged is neither derivation ---
                    // the bound was already a reachable sum, so there was
                    // nothing to derive --- and counting it as a dynamic
                    // programme would say the expensive path ran when no line
                    // was written at all.
                    if (strengthened.line == source)
                        recipe_logger.emit_proof_comment("presolve cumulative kappa already reached");
                    else {
                        recipe_logger.emit_proof_comment(strengthened.by_division ? "presolve cumulative gcd" : "presolve cumulative kappa");
                        if (strengthened.by_division)
                            ++stats->rows_by_division;
                        else
                            ++stats->rows_by_dynamic_programming;
                    }
                    return strengthened.line;
                };

                // Nothing fills the resource here, so this is the capacity rule
                // on its own and the row is the donor's, strengthened. Landing
                // it on the declared capacity rather than on this time point's
                // own largest load is what makes the rows uniform --- and the
                // step is an implication check, which is syntactic, so it is
                // the one thing that notices a derivation landing somewhere
                // other than where it claimed: a divisor that does not divide
                // every height still divides *soundly*, and nothing else in the
                // proof would object.
                if (full_here.empty()) {
                    auto strengthened = strengthen_to_kappa(donor_row);
                    return recipe_logger.emit(ImpliesProofRule{strengthened}, move(load) <= kappa, ProofLevel::Top);
                }

                recipe_logger.emit_proof_comment("presolve cumulative amo");

                // The at-most-ones, each out of the donor's own row: a raised
                // task conflicts with everything, so every pair it is in has
                // one. Cached, because a pair of raised tasks needs the same
                // line from both directions.
                map<pair<size_t, size_t>, ProofLine> at_most_ones;
                auto at_most_one_between = [&](size_t a, size_t b) -> ProofLine {
                    auto key = pair{min(a, b), max(a, b)};
                    auto already = at_most_ones.find(key);
                    if (already != at_most_ones.end())
                        return already->second;

                    vector<ProofFlag> weaken_out;
                    for (auto i : full_here)
                        if (i != a && i != b)
                            weaken_out.push_back(flag_for(i));
                    for (auto i : point->second.tasks)
                        if (i != a && i != b)
                            weaken_out.push_back(flag_for(i));

                    // Under the unentitled-raise mutation a pair that fits has
                    // nothing to recover, and the routine refuses. Reporting a
                    // demand large enough to overshoot by one keeps the step
                    // legal so that what fails is the claim the row finally
                    // makes, which is the point of running the mutation at all
                    // --- and lying about the demand is the more faithful lie,
                    // since the mutation's whole content is a conflict that is
                    // not there.
                    auto demand_a = heights[a];
                    if (unentitled_raise && heights[a] + heights[b] <= capacity)
                        demand_a = capacity - heights[b] + 1_i;

                    auto recovered =
                        recover_am1_from_row(recipe_logger, donor_row, {demand_a, heights[b]}, weaken_out, capacity, ProofLevel::Temporary);
                    // An at-most-one is what the raise arithmetic below assumes
                    // it has --- it weights these lines by the other task's
                    // coefficient and divides --- and a cardinality bound of
                    // anything else would make it argue about a line that says
                    // something different. It cannot be anything else: the
                    // pairwise case gives a bound of one whenever the smaller
                    // demand fits under the capacity, and a donor with a task
                    // over the capacity was declined 350 lines ago. Checked
                    // rather than assumed, because that is a long way to have
                    // to look for the reason.
                    if (recovered.at_most != 1_i)
                        throw ProofError{"cumulative strengthening: recovering the at-most-one between tasks " + to_string(a) + " and " +
                            to_string(b) + " gave a bound of " + to_string(recovered.at_most.raw_value) + " rather than one"};
                    at_most_ones.emplace(key, recovered.line);
                    return recovered.line;
                };

                // The row the raised tasks go into, derived on demand. Only the
                // step-by-step raise below needs it, and only when the rest of
                // the row overshoots the capacity, so a time point where
                // everything else fits alongside pays for no subset sum at all
                // --- the at-most-ones are the whole argument there.
                optional<ProofLine> row;
                auto row_to_raise_into = [&]() -> ProofLine {
                    if (row)
                        return *row;

                    // The raised tasks come out of the donor's row first, which
                    // is the whole point of setting them aside: a task that
                    // reaches the capacity on its own makes the largest
                    // reachable load the capacity, and the subset sum then has
                    // nothing to say.
                    PolBuilder without_full;
                    without_full.add(donor_row);
                    for (auto i : full_here)
                        without_full.weaken(flag_for(i), tracker);
                    row = strengthen_to_kappa(without_full.emit(recipe_logger, ProofLevel::Temporary));

                    // A time point whose own largest load is below the declared
                    // capacity has to be relaxed up to it *before* anything is
                    // raised into it, rather than at the end: a raise keeps
                    // whatever right hand side it is given, and it can raise a
                    // coefficient no higher, so a row left on the smaller one
                    // would neither reach kappa nor pin to it.
                    if (point->second.kappa < kappa) {
                        WPBSum rest;
                        for (const auto & item : items)
                            rest += item.coefficient * std::get<ProofFlag>(item.term);
                        row = recipe_logger.emit(ImpliesProofRule{*row}, move(rest) <= kappa, ProofLevel::Temporary);
                    }
                    return *row;
                };

                // Then the raised tasks, one at a time, each into the row the
                // last one left behind. Ordered, so that the `pol` text depends
                // on the fixture and not on where the heap put things.
                map<size_t, Integer> running;
                for (auto i : point->second.tasks)
                    running.emplace(i, heights[i]);

                for (auto task : full_here) {
                    auto total = std::accumulate(
                        running.begin(), running.end(), 0_i, [](Integer so_far, const auto & entry) { return so_far + entry.second; });

                    if (total == 0_i) {
                        // Nothing else can run here at all, so there is no row
                        // to raise into and no at-most-one to do it with: the
                        // claim is only that a flag is at most one.
                        WPBSum alone;
                        alone += kappa * flag_for(task);
                        row = recipe_logger.emit_rup_proof_line(move(alone) <= kappa, ProofLevel::Temporary);
                        ++stats->raise_lines_emitted;
                    }
                    else if (total <= kappa) {
                        // Everything else fits alongside, so the at-most-ones
                        // summed are already the row --- at a right hand side
                        // of `total`, which the implication step then relaxes
                        // to kappa.
                        PolBuilder summed;
                        for (const auto & [other, weight] : running)
                            summed.add(at_most_one_between(task, other), weight);
                        row = summed.emit(recipe_logger, ProofLevel::Temporary);
                        ++stats->raise_lines_emitted;

                        if (total < kappa) {
                            WPBSum raised;
                            raised += kappa * flag_for(task);
                            for (const auto & [other, weight] : running)
                                raised += weight * flag_for(other);
                            row = recipe_logger.emit(ImpliesProofRule{*row}, move(raised) <= kappa, ProofLevel::Temporary);
                        }
                    }
                    else {
                        auto steps = raise_steps(total, kappa);
                        auto raised_to = 0_i;
                        for (size_t s = 0; s < steps.size(); ++s) {
                            auto step = steps[s];
                            if (raise_too_fast && s == 0) {
                                // Only the first step is corrupted; the rest of
                                // the sequence then compounds it honestly,
                                // which is what a step-size rule getting lost
                                // in a rearrangement would look like.
                                if (step + 1_i > min(kappa - raised_to, total - raised_to - 1_i))
                                    throw ProofError{"cumulative strengthening: the raise-too-fast mutation needs a raise with a step to spare, "
                                                     "and this one does not"};
                                step += 1_i;
                            }

                            // `lambda` copies of the row so far, plus each
                            // at-most-one weighted by its task's coefficient in
                            // that row, scaled so that the division comes out
                            // whole on every term but the degree.
                            //
                            // `e * weight` is a product of two quantities each
                            // bounded by the capacity, so it is the capacity
                            // limit at the top of run() that keeps this inside
                            // a `long long` --- an unbounded capacity would
                            // reach it a good deal sooner than anything here
                            // looks like it could.
                            auto rest = total - raised_to - step;
                            auto common = Integer{std::gcd(step.raw_value, rest.raw_value)};
                            auto e = step / common, lambda = rest / common;

                            PolBuilder raise;
                            raise.add(row_to_raise_into(), lambda);
                            for (const auto & [other, weight] : running)
                                raise.add(at_most_one_between(task, other), e * weight);
                            raise.divide_by(lambda + e);
                            row = raise.emit(recipe_logger, ProofLevel::Temporary);
                            ++stats->raise_lines_emitted;

                            raised_to += step;
                        }
                    }

                    running.emplace(task, kappa);
                }

                ++stats->rows_with_a_raise;

                return recipe_logger.emit(ImpliesProofRule{*row}, move(load) <= kappa, ProofLevel::Top);
            },
            .rules = _rules,
            // A share of this block's own sub-block, so that every donor's
            // install adds to one aggregate rather than registering a component
            // apiece.
            .stats = shared_ptr<DerivedCumulativeStats>{_stats, &_stats->derived}};

        // After the install rather than before it: a decline writes nothing at
        // all, and a proof saying a constraint was strengthened when it was not
        // is worse than one saying nothing.
        if (! install_derived_cumulative(propagators, state, logger, move(spec))) {
            // A state that cannot happen, so it throws rather than being
            // counted: the rows here are derived over the donor's *own*
            // windows, so the flags install_derived_cumulative goes looking for
            // are ones the donor published. A note for a bug is a note nobody
            // reads.
            //
            // With one exception, which is a restriction rather than a bug: a
            // proof written with assertions on omits definitions, so a task
            // with both a variable start and a variable length has no
            // end-of-task line to pin `after` through and the install declines
            // for a reason this presolver cannot do anything about.
            if (logger && logger->get_assertion_level() != AssertionLevel::Off)
                continue;
            throw UnexpectedException{"cumulative strengthening: install_derived_cumulative declined " + as_string(donor_id) +
                ", whose rows were derived over the donor's own windows"};
        }

        if (logger)
            logger->emit_proof_comment("presolve cumulative: strengthened " + as_string(donor_id) + " from capacity " +
                to_string(capacity.raw_value) + " to " + to_string(kappa.raw_value) + ", raising " + to_string(full_tasks.size()) +
                " heights to the capacity");

        bump(&CumulativeStrengtheningStats::donors_strengthened);
        _stats->capacity_units_removed += capacity - kappa;
        _stats->tasks_raised += full_tasks.size();
    }

    // The model-level consequence, for a reader who does not know what this
    // presolver is: a limit stopped it doing what it was asked to do, so the
    // configuration being run is not the one that was asked for. The figures
    // and the constraint each decline is about are in the General notes above;
    // this one names neither, because naming them is what makes a message
    // unreadable to the person it is for.
    if (0 != limit_declines_this_run)
        note(StatsLevel::Important, nullopt,
            "Cumulative strengthening was skipped on " + to_string(limit_declines_this_run) + " of " +
                to_string(_stats->donors_seen - donors_before) +
                " constraints because a size limit was reached; answers are still correct, but search may be slower");

    return true;
}

auto CumulativeStrengthening::clone() const -> unique_ptr<Presolver>
{
    auto result = make_unique<CumulativeStrengthening>(_stats);
    result->with_dynamic_programming_budget(_max_dynamic_programming_states);
    result->with_raise_budget(_max_raise_lines);
    result->with_subset_sum_capacity_limit(_max_subset_sum_capacity);
    result->with_rules(_rules);
    result->with_proof_mutation(_mutation);
    return result;
}

auto CumulativeStrengtheningStats::component_name() const -> std::string
{
    return "cumulative_strengthening";
}

auto CumulativeStrengtheningStats::summary() const -> std::string
{
    if (0 == donors_seen)
        return "no posted Cumulative to look at";

    if (0 == donors_strengthened)
        return "nothing strengthened, of " + to_string(donors_seen) + " posted Cumulative" + (1 == donors_seen ? "" : "s") + " looked at";

    return to_string(donors_strengthened) + " of " + to_string(donors_seen) + " posted Cumulatives strengthened, taking " +
        to_string(capacity_units_removed.raw_value) + " off their capacities and raising " + to_string(tasks_raised) + " heights";
}

auto CumulativeStrengtheningStats::entries() const -> vector<StatsEntry>
{
    vector<StatsEntry> result;
    auto add = [&](const char * name, size_t value) { result.push_back(StatsEntry{name, static_cast<long long>(value)}); };

    add("donors_seen", donors_seen);
    add("donors_strengthened", donors_strengthened);
    result.push_back(StatsEntry{"capacity_units_removed", capacity_units_removed.raw_value});
    add("donors_with_set_aside_tasks", donors_with_set_aside_tasks);
    add("donors_better_off_setting_heights_aside", donors_better_off_setting_heights_aside);
    add("converted_heights", converted_heights);
    add("tasks_raised", tasks_raised);
    add("declined_irreducible_capacity", declined_irreducible_capacity);
    add("declined_infeasible_donor", declined_infeasible_donor);
    add("declined_capacity_too_large", declined_capacity_too_large);
    add("declined_over_budget", declined_over_budget);
    add("declined_over_raise_budget", declined_over_raise_budget);
    add("declined_nothing_to_gain", declined_nothing_to_gain);
    add("rows_by_division", rows_by_division);
    add("rows_by_dynamic_programming", rows_by_dynamic_programming);
    add("rows_with_a_raise", rows_with_a_raise);
    add("raise_lines_emitted", raise_lines_emitted);
    derived.add_entries_to(result, "derived_");

    return result;
}
