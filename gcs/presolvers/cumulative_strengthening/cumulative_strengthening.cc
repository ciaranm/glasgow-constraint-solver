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
#include <gcs/innards/proofs/subset_sum_strengthening.hh>
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
using std::make_unique;
using std::map;
using std::max;
using std::min;
using std::move;
using std::optional;
using std::pair;
using std::shared_ptr;
using std::size_t;
using std::to_string;
using std::unique_ptr;
using std::vector;

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
    /// the budget and the derivation call the same function --- a prediction
    /// that disagreed would decline the wrong donors.
    [[nodiscard]] auto raise_steps(Integer total, Integer kappa) -> vector<Integer>
    {
        // Everything else fits alongside, so the at-most-ones alone say it:
        // summed, they give the whole row in one `pol`, and there is no
        // division to survive.
        if (total <= kappa)
            return {kappa};

        auto overshoot = total - kappa;
        vector<Integer> steps;
        for (auto c = 0_i; c < kappa;) {
            // ceil((total - c) / overshoot) - 1, which is at least one while
            // `c < kappa`, so this terminates.
            auto step = min(kappa - c, (total - c + overshoot - 1_i) / overshoot - 1_i);
            steps.push_back(step);
            c += step;
        }
        return steps;
    }
}

CumulativeStrengthening::CumulativeStrengthening(shared_ptr<CumulativeStrengtheningStats> stats) :
    _stats(move(stats)), _max_dynamic_programming_states(20000), _max_raise_lines(5000),
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
    auto bump = [&](size_t CumulativeStrengtheningStats::* field) {
        if (_stats)
            ++((*_stats).*field);
    };

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
            bump(&CumulativeStrengtheningStats::declined_variable_arguments);
            if (logger)
                logger->emit_proof_comment("presolve cumulative: declining " + as_string(donor.constraint_id()) + ", capacity is not reducible");
            continue;
        }
        if (! view->set_aside.empty())
            bump(&CumulativeStrengtheningStats::donors_with_set_aside_tasks);

        const auto & starts = donor.starts();
        auto n = starts.size();
        auto capacity = view->capacity;

        // The same windowing install_derived_cumulative resolves, and the same
        // windowing the donor encoded: a task can be active from its earliest
        // start to its latest finish, which for a variable duration is the
        // largest one still allowed. This is the paper's `t in [est_j, lct_j)`.
        vector<Integer> t_lo(n, 0_i), t_hi(n, 0_i);
        const auto & active_tasks = view->usable;
        for (auto i : active_tasks) {
            auto [s_lo, s_hi] = state.bounds(starts[i]);
            t_lo[i] = s_lo;
            t_hi[i] = s_hi + state.upper_bound(view->lengths[i]) - 1_i;
        }

        if (active_tasks.empty()) {
            bump(&CumulativeStrengtheningStats::declined_nothing_to_gain);
            continue;
        }

        // A height above the capacity means the donor is infeasible on its own,
        // which is the donor's business to detect and not something to build a
        // subset sum over.
        if (std::any_of(active_tasks.begin(), active_tasks.end(), [&](size_t i) { return view->heights[i] > capacity; })) {
            bump(&CumulativeStrengtheningStats::declined_nothing_to_gain);
            continue;
        }

        // Schulz's coefficient raising, as the set of tasks it applies to. A
        // task that cannot run beside any *other* task that consumes anything
        // occupies the resource whenever it runs, whatever its height says, so
        // its height is really the capacity --- and, once the capacity comes
        // down to kappa below, really kappa.
        //
        // Stated as the pairwise test rather than as the paper's
        // `c_i > C - min_j c_j`, because the two are the same condition and the
        // pairwise one is what the certificate needs anyway: it is one
        // at-most-one per pair, each derived from the donor's own row. Tasks
        // whose windows cannot overlap are not part of it, which is a little
        // more than the paper claims and costs nothing --- if they can never be
        // active together, no row ever mentions both.
        //
        // Deliberately *not* per time point, even though fewer tasks can run at
        // one time point than over the whole horizon and the set would be
        // larger for it: a Cumulative has one height per task, not one per time
        // point, so a task that only fills the resource at some of them cannot
        // be given a raised height at all.
        vector<size_t> full_tasks, other_tasks;
        for (auto i : active_tasks) {
            auto conflicts_with_everything = std::all_of(active_tasks.begin(), active_tasks.end(),
                [&](size_t j) { return i == j || t_hi[i] < t_lo[j] || t_hi[j] < t_lo[i] || view->heights[i] + view->heights[j] > capacity; });
            (conflicts_with_everything ? full_tasks : other_tasks).push_back(i);
        }

        // The mutation that says the pairwise test is the load-bearing part:
        // take the tallest task that did *not* qualify and raise it anyway.
        // Everything downstream then runs honestly on a set that is wrong, and
        // the row it lands on is a row the donor does not imply.
        auto unentitled_raise = std::holds_alternative<cumulative_strengthening_mutation::RaiseUnentitled>(_mutation);
        if (unentitled_raise && ! other_tasks.empty()) {
            auto tallest =
                std::max_element(other_tasks.begin(), other_tasks.end(), [&](size_t a, size_t b) { return view->heights[a] < view->heights[b]; });
            full_tasks.push_back(*tallest);
            other_tasks.erase(tallest);
            std::sort(full_tasks.begin(), full_tasks.end());
        }

        auto global_lo = t_lo[active_tasks.front()], global_hi = t_hi[active_tasks.front()];
        for (auto i : active_tasks) {
            global_lo = min(global_lo, t_lo[i]);
            global_hi = max(global_hi, t_hi[i]);
        }

        vector<TimePoint> time_points;
        auto kappa = 0_i;
        for (Integer t = global_lo; t <= global_hi; ++t) {
            TimePoint point{t, {}, {}, {}, 0_i, false};
            for (auto i : other_tasks)
                if (t >= t_lo[i] && t <= t_hi[i]) {
                    point.tasks.push_back(i);
                    point.heights.push_back(view->heights[i]);
                }
            for (auto i : full_tasks)
                if (t >= t_lo[i] && t <= t_hi[i])
                    point.full_tasks.push_back(i);

            // No task can be active here, so the donor wrote no row and there is
            // nothing to derive from.
            if (point.tasks.empty() && point.full_tasks.empty())
                continue;

            point.kappa = largest_subset_sum_at_most(point.heights, capacity);

            auto divisor = 0_i;
            for (const auto & h : point.heights)
                divisor = Integer{std::gcd(divisor.raw_value, h.raw_value)};
            point.by_division = (divisor > 1_i && divisor * (capacity / divisor) == point.kappa);

            kappa = max(kappa, point.kappa);
            time_points.push_back(move(point));
        }

        // Every task fills the resource on its own, so the tasks the capacity
        // is a subset sum *of* are none of them and kappa is zero. That is not
        // a strengthening but a disjunctive, and inferring those from conflict
        // cliques is what the InferredDisjunctive presolver does.
        if (kappa <= 0_i) {
            bump(&CumulativeStrengtheningStats::declined_nothing_to_gain);
            continue;
        }

        // kappa is the largest load reachable at any one time point once the
        // tasks that fill the resource are set aside, so it is what the
        // capacity really is. If that is the capacity already, and no task's
        // height changes either, the donor was posted with the numbers it
        // deserved and there is nothing here.
        auto raises_a_height = std::any_of(full_tasks.begin(), full_tasks.end(), [&](size_t i) { return view->heights[i] != kappa; });
        if (kappa >= capacity && ! raises_a_height) {
            bump(&CumulativeStrengtheningStats::declined_nothing_to_gain);
            continue;
        }

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

                auto total = std::accumulate(point.heights.begin(), point.heights.end(), 0_i);
                for (size_t taken = 0; taken < point.full_tasks.size(); ++taken) {
                    raise_lines += static_cast<long long>(raise_steps(total, kappa).size());
                    total += kappa;
                }
            }

            if (states > _max_dynamic_programming_states) {
                bump(&CumulativeStrengtheningStats::declined_over_budget);
                logger->emit_proof_comment("presolve cumulative: declining " + as_string(donor.constraint_id()) + ", derivation would need " +
                    to_string(states) + " dynamic programming states against a budget of " + to_string(_max_dynamic_programming_states));
                continue;
            }

            if (raise_lines > _max_raise_lines) {
                bump(&CumulativeStrengtheningStats::declined_over_raise_budget);
                logger->emit_proof_comment("presolve cumulative: declining " + as_string(donor.constraint_id()) + ", raising heights would need " +
                    to_string(raise_lines) + " proof lines against a budget of " + to_string(_max_raise_lines));
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
        SubsetSumMutation subset_sum_corruption = std::visit(
            overloaded{//
                [](const cumulative_strengthening_mutation::ClaimOneBetter &) -> SubsetSumMutation { return subset_sum_mutation::ClaimOneBetter{}; },
                [](const cumulative_strengthening_mutation::BogusDivisor &) -> SubsetSumMutation { return subset_sum_mutation::BogusDivisor{}; },
                [](const auto &) -> SubsetSumMutation { return subset_sum_mutation::None{}; }},
            _mutation);
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
                auto saved_level = recipe_logger.proof_level();
                recipe_logger.enter_proof_level(saved_level + 1);
                auto give_back = [&](optional<ProofLine> line) {
                    recipe_logger.enter_proof_level(saved_level);
                    recipe_logger.forget_proof_level(saved_level + 2);
                    return line;
                };

                // The row everything below argues from, reduced to the
                // constant-argument form it reads it as: the set-aside tasks'
                // terms weakened away, and a variable capacity replaced by the
                // number `capacity` already holds. Working like the rest, so it
                // goes inside the level that gets forgotten.
                auto reduced_row = recover_constant_argument_row(recipe_logger, view, donor_id, donor_row_at->second, t, ProofLevel::Temporary);
                if (! reduced_row)
                    return give_back(std::nullopt);
                auto donor_row = *reduced_row;

                auto strengthen_to_kappa = [&](ProofLine source) -> ProofLine {
                    recipe_logger.emit_proof_comment(point->second.by_division ? "presolve cumulative gcd" : "presolve cumulative kappa");
                    auto strengthened =
                        derive_subset_sum_strengthening(recipe_logger, items, source, capacity, ProofLevel::Temporary, subset_sum_corruption);
                    if (stats) {
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
                    return give_back(recipe_logger.emit(ImpliesProofRule{strengthened}, move(load) <= kappa, ProofLevel::Top));
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
                        if (stats)
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
                        if (stats)
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
                            auto rest = total - raised_to - step;
                            auto common = Integer{std::gcd(step.raw_value, rest.raw_value)};
                            auto e = step / common, lambda = rest / common;

                            PolBuilder raise;
                            raise.add(row_to_raise_into(), lambda);
                            for (const auto & [other, weight] : running)
                                raise.add(at_most_one_between(task, other), e * weight);
                            raise.divide_by(lambda + e);
                            row = raise.emit(recipe_logger, ProofLevel::Temporary);
                            if (stats)
                                ++stats->raise_lines_emitted;

                            raised_to += step;
                        }
                    }

                    running.emplace(task, kappa);
                }

                if (stats)
                    ++stats->rows_with_a_raise;

                return give_back(recipe_logger.emit(ImpliesProofRule{*row}, move(load) <= kappa, ProofLevel::Top));
            },
            .rules = _rules};

        // After the install rather than before it: a decline writes nothing at
        // all, and a proof saying a constraint was strengthened when it was not
        // is worse than one saying nothing.
        if (! install_derived_cumulative(propagators, state, logger, move(spec))) {
            bump(&CumulativeStrengtheningStats::declined_by_install);
            continue;
        }

        if (logger)
            logger->emit_proof_comment("presolve cumulative: strengthened " + as_string(donor_id) + " from capacity " +
                to_string(capacity.raw_value) + " to " + to_string(kappa.raw_value) + ", raising " + to_string(full_tasks.size()) +
                " heights to the capacity");

        bump(&CumulativeStrengtheningStats::donors_strengthened);
        if (_stats) {
            _stats->capacity_units_removed += capacity - kappa;
            _stats->tasks_raised += full_tasks.size();
        }
    }

    return true;
}

auto CumulativeStrengthening::clone() const -> unique_ptr<Presolver>
{
    auto result = make_unique<CumulativeStrengthening>(_stats);
    result->with_dynamic_programming_budget(_max_dynamic_programming_states);
    result->with_raise_budget(_max_raise_lines);
    result->with_rules(_rules);
    result->with_proof_mutation(_mutation);
    return result;
}
