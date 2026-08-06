#include <gcs/constraint_id.hh>
#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/cumulative/derived_cumulative.hh>
#include <gcs/constraints/cumulative/donor_view.hh>
#include <gcs/innards/proofs/flag_bridge.hh>
#include <gcs/innards/proofs/lifted_cover_cut.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/state.hh>
#include <gcs/presolvers/inferred_cumulative/inferred_cumulative.hh>
#include <gcs/presolvers/innards/makespan_links.hh>
#include <gcs/problem.hh>
#include <util/overloaded.hh>

#include <algorithm>
#include <map>
#include <memory>
#include <numeric>
#include <optional>
#include <set>
#include <string>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_shared;
using std::make_unique;
using std::map;
using std::max;
using std::min;
using std::move;
using std::optional;
using std::pair;
using std::set;
using std::shared_ptr;
using std::size_t;
using std::to_string;
using std::unique_ptr;
using std::vector;
using std::ranges::any_of;

namespace
{
    /// One posted Cumulative a cut can be lifted over.
    struct Donor
    {
        ConstraintID id;
        size_t size;
        Integer capacity;
        /// What of this donor can be argued over: which of its tasks have a
        /// constant term in its rows, and what its capacity comes to. A recipe
        /// needs it to reduce those rows before lifting anything out of them.
        CumulativeDonorView view;
    };

    /// One task, as it appears across every donor.
    ///
    /// Sidorov's Equation 4 constrains over all of the resources at once, so
    /// what the procedure works on is a matrix rather than a row: one column per
    /// task, one row per resource. Tasks are matched across posted constraints
    /// by their start variable and length, which is what his
    /// `extract_cumulative_matrix` does with the interval expressions, and two
    /// of a donor's own tasks that look the same stay separate rather than being
    /// folded into one column.
    struct Task
    {
        IntegerVariableID start;
        Integer length;
        Integer t_lo, t_hi;

        /// Per donor: what this task takes, and where it sits in that donor's
        /// task list. Absent where the donor has no such task, and zero where it
        /// has one that consumes nothing --- which is not the same thing, since
        /// only the first means there is no flag to speak with.
        vector<Integer> demands;
        vector<optional<size_t>> positions;

        /// The donor whose flags speak for this task: the first one that gives
        /// it a term of its own. A cut's members can perfectly well take theirs
        /// from different donors, which is what DerivedCumulativeTask naming a
        /// donor per task is for.
        size_t canonical_donor;
    };

    /// A lifted cover inequality over some tasks: `sum_i coefficients[i] a_i <=
    /// rhs`, with `support` indexing into the joint task list.
    struct Cut
    {
        vector<size_t> support;
        vector<Integer> coefficients;
        Integer rhs;
        /// The dynamic programme over the whole support, which is what says the
        /// cut holds. Kept rather than rebuilt: the row every time point in the
        /// middle of the window needs is this one, and only the restrictions at
        /// the edges have members missing.
        optional<LiftedCoverCut> validated;
        /// `sum_i d_i pi_i`, the energy the cut's tasks need out of a resource
        /// supplying `rhs` per time step. Kept rather than recomputed, so the
        /// number ranking the cuts is the number reported.
        Integer energy;

        [[nodiscard]] auto bound() const -> Integer
        {
            return (energy + rhs - 1_i) / rhs;
        }
    };

    [[nodiscard]] auto constant_value_of(const IntegerVariableID & v) -> optional<Integer>
    {
        if (! is_constant_variable(v))
            return std::nullopt;
        return std::get<ConstantIntegerVariableID>(v).const_value;
    }

    /// A task's activity flag on a donor at one time, absent when that donor
    /// never encoded the pair --- which is how a task outside its window looks,
    /// and is also how it looks in the donor's own capacity row.
    [[nodiscard]] auto active_flag_for(const NamesAndIDsTracker & tracker, const ConstraintID & donor, size_t position, Integer t)
        -> optional<ProofFlag>
    {
        return tracker.find_proof_flag_values(donor, ConstraintProofModelData<Cumulative>::active_flag_key(position, t));
    }

    /// The `before` and `after` flags an `active` flag is the conjunction of,
    /// which is what a bridge between two donors' copies of it has to line up.
    [[nodiscard]] auto active_conjuncts_for(const NamesAndIDsTracker & tracker, const ConstraintID & donor, size_t position, Integer t)
        -> optional<vector<ProofFlag>>
    {
        auto before = tracker.find_proof_flag_values(donor, ConstraintProofModelData<Cumulative>::before_flag_key(position, t));
        auto after = tracker.find_proof_flag_values(donor, ConstraintProofModelData<Cumulative>::after_flag_key(position, t));
        if (! before || ! after)
            return std::nullopt;
        return vector<ProofFlag>{*before, *after};
    }

    /// Algorithm 1 of Sidorov (CP 2026), for one resource. Two families.
    ///
    /// **Short covers**: every pair whose demands overshoot, and --- for each
    /// pair that does *not* --- that pair plus the longest-duration task big
    /// enough to push it over. Covers are then ranked by the capacity bound of
    /// their own cover inequality, `sum_i d_i / (|C| - 1)`, and the best
    /// `max_covers` kept. Lifting is what grows them; they do not need to be
    /// large to start with.
    ///
    /// **Long covers**: for each distinct demand `v`, the smallest `k` with
    /// `k*v > C`, taking the `k` longest and the `k` shortest tasks of that
    /// demand. Only for `cover_cardinality` of four or more, since two and
    /// three are covered above.
    ///
    /// The reference implementation compares a duration against an *index* when
    /// picking the longest task of a given demand (`durations[ix] >
    /// inv_A_longest[a]`); Sidorov confirms the intended line is
    /// `durations[ix] > durations[inv_A_longest[a]]`, which is what happens
    /// here. Its published results came from the shipped line, so the ternary
    /// covers here are not the ones its numbers were produced from --- never
    /// worse ones, which is the awkward direction. See the writeup.
    [[nodiscard]] auto collect_covers(const vector<Task> & tasks, const vector<Integer> & demands, Integer capacity, size_t max_covers,
        size_t cover_cardinality) -> vector<vector<size_t>>
    {
        auto n = tasks.size();
        map<Integer, vector<size_t>> by_demand;
        for (size_t i = 0; i < n; ++i)
            if (demands[i] > 0_i)
                by_demand[demands[i]].push_back(i);

        map<Integer, size_t> longest_of_demand;
        for (const auto & [demand, group] : by_demand) {
            auto longest = group.front();
            for (auto i : group)
                if (tasks[i].length > tasks[longest].length)
                    longest = i;
            longest_of_demand.emplace(demand, longest);
        }

        set<vector<size_t>> seen;
        vector<vector<size_t>> covers;
        auto remember = [&](vector<size_t> cover) {
            std::sort(cover.begin(), cover.end());
            if (seen.insert(cover).second)
                covers.push_back(move(cover));
        };

        for (size_t x = 0; x < n; ++x)
            for (size_t y = x + 1; y < n; ++y)
                if (demands[x] + demands[y] > capacity)
                    remember({x, y});

        if (cover_cardinality >= 3)
            for (size_t x = 0; x < n; ++x)
                for (size_t y = x + 1; y < n; ++y) {
                    if (demands[x] <= 0_i || demands[y] <= 0_i)
                        continue;
                    auto room = capacity - demands[x] - demands[y];
                    if (room < 0_i)
                        continue;
                    for (const auto & [demand, z] : longest_of_demand)
                        if (demand > room && z != x && z != y)
                            remember({x, y, z});
                }

        // The capacity bound of the cover inequality itself, which is what the
        // covers are ranked by: unit coefficients over a right-hand side of
        // |C| - 1.
        auto bound_of = [&](const vector<size_t> & cover) {
            auto total = 0_i;
            for (auto i : cover)
                total += tasks[i].length;
            return pair{total, Integer{static_cast<long long>(cover.size()) - 1}};
        };
        std::sort(covers.begin(), covers.end(), [&](const vector<size_t> & a, const vector<size_t> & b) {
            auto [ta, ra] = bound_of(a);
            auto [tb, rb] = bound_of(b);
            if (ta * rb != tb * ra)
                return ta * rb > tb * ra;
            return a < b;
        });
        if (covers.size() > max_covers)
            covers.resize(max_covers);

        // The long covers are added *after* the budget has been applied, so the
        // budget caps the short families only --- and the duplicate check has
        // to be rebuilt against what survived, or a long cover identical to a
        // short one the budget just dropped would be lost with it.
        seen.clear();
        seen.insert(covers.begin(), covers.end());

        if (cover_cardinality >= 4)
            for (const auto & [demand, group] : by_demand) {
                if (demand <= 0_i)
                    continue;
                auto size = static_cast<size_t>(((capacity + 1_i + demand - 1_i) / demand).raw_value);
                if (size <= 2 || size > cover_cardinality || size > group.size())
                    continue;
                auto by_length = group;
                std::sort(by_length.begin(), by_length.end(), [&](size_t a, size_t b) {
                    if (tasks[a].length != tasks[b].length)
                        return tasks[a].length > tasks[b].length;
                    return a < b;
                });
                remember(vector<size_t>(by_length.begin(), by_length.begin() + static_cast<long>(size)));
                remember(vector<size_t>(by_length.end() - static_cast<long>(size), by_length.end()));
            }

        // Covers of more than three tasks go first, as they do in the reference
        // implementation: they are the ones the short-cover families cannot
        // produce, and the visited-cover skip would otherwise let a ternary
        // cover's lifted support swallow them.
        std::stable_sort(
            covers.begin(), covers.end(), [](const vector<size_t> & a, const vector<size_t> & b) { return (a.size() > 3) && (b.size() <= 3); });

        return covers;
    }

    /// The lifting subproblem `v*` of Sidorov Equation 4: the most the current
    /// inequality's left-hand side can weigh over the variables already in it,
    /// once `member` is forced to run and has taken its demand off every
    /// resource.
    ///
    /// This is a multi-dimensional knapsack, and it is answered by the very
    /// programme that will certify the finished cut --- indexed by profit, and
    /// capped at the right-hand side, because a `v*` that reaches it leaves no
    /// positive coefficient to lift with and the exact value stops mattering.
    /// Sharing that machinery is not an economy: it is what makes a cut the
    /// procedure infers one the proof can reach, since both are asking the same
    /// question of the same rows.
    struct Subproblem
    {
        optional<Integer> optimum;
        bool over_budget = false;
    };

    [[nodiscard]] auto lifting_subproblem(const vector<vector<Integer>> & demands, const vector<Integer> & capacities,
        const vector<Integer> & coefficients, const vector<size_t> & support, size_t member, Integer rhs, size_t state_budget) -> Subproblem
    {
        vector<Integer> residual, support_coefficients;
        vector<vector<Integer>> support_demands(capacities.size());
        for (size_t row = 0; row < capacities.size(); ++row) {
            residual.push_back(capacities[row] - demands[row][member]);
            if (residual.back() < 0_i)
                return Subproblem{0_i, false};
            for (auto i : support)
                support_demands[row].push_back(demands[row][i]);
        }
        for (auto i : support)
            support_coefficients.push_back(coefficients[i]);

        auto answer = lifted_cover_cut_optimum(support_demands, support_coefficients, residual, rhs, state_budget);
        return Subproblem{answer.value, answer.over_state_budget};
    }

    /// Algorithm 2's inner loop: start from the cover inequality
    /// `sum_C x_i <= |C| - 1` and lift every other task into it, longest
    /// duration first, each with the largest coefficient the subproblem allows.
    /// The right-hand side never moves.
    ///
    /// Longest first follows the reference implementation, which sorts by
    /// duration descending; the paper's Algorithm 2 says `arg min d_i`, and
    /// Sidorov confirms that is the typo. Bringing the tasks with the biggest
    /// effect on the bound in first keeps them out of the subproblem's objective
    /// while it is still small, so they meet a smaller `v*` and get a larger
    /// coefficient. Lifting is sequence-dependent even over one row (Zemel
    /// 1978), so the order is load-bearing rather than cosmetic.
    struct Lifted
    {
        vector<Integer> coefficients;
        Integer rhs;
        size_t subproblems;
        size_t over_budget;
    };

    [[nodiscard]] auto lift_cover(const vector<Task> & tasks, const vector<vector<Integer>> & demands, const vector<Integer> & capacities,
        const vector<size_t> & cover, size_t budget, size_t state_budget) -> Lifted
    {
        vector<Integer> coefficients(tasks.size(), 0_i);
        for (auto i : cover)
            coefficients[i] = 1_i;
        auto rhs = Integer{static_cast<long long>(cover.size()) - 1};

        vector<size_t> remaining;
        for (size_t i = 0; i < tasks.size(); ++i)
            if (std::find(cover.begin(), cover.end(), i) == cover.end())
                remaining.push_back(i);
        std::sort(remaining.begin(), remaining.end(), [&](size_t a, size_t b) {
            if (tasks[a].length != tasks[b].length)
                return tasks[a].length > tasks[b].length;
            return a < b;
        });

        auto support = cover;
        size_t used = 0, over_budget = 0;
        for (auto member : remaining) {
            if (used >= budget)
                break;
            ++used;
            auto subproblem = lifting_subproblem(demands, capacities, coefficients, support, member, rhs, state_budget);
            if (subproblem.over_budget) {
                // No answer means no coefficient: the task is left out, which
                // weakens the cut rather than invalidating it. Counted, because
                // a constraint that differs from the published procedure's is
                // worth knowing about even when it is still sound.
                ++over_budget;
                continue;
            }
            // A subproblem that reaches the right-hand side leaves nothing
            // positive to lift with, and the reference implementation warns
            // about the negative coefficient rather than trusting it.
            if (! subproblem.optimum)
                continue;
            auto lifted = rhs - *subproblem.optimum;
            if (lifted <= 0_i)
                continue;
            coefficients[member] = lifted;
            support.push_back(member);
        }

        return Lifted{move(coefficients), rhs, used, over_budget};
    }

    /// One member of a cut, as the per-time recipe needs to see it.
    struct RecipeMember
    {
        /// Where its flags come from, and where it sits there.
        size_t canonical_donor;
        size_t canonical_position;
        /// Per donor, as in Task.
        vector<Integer> demands;
        vector<optional<size_t>> positions;
        Integer coefficient, t_lo, t_hi;
    };

    /// Everything the per-time recipe needs, copied out of the presolver so the
    /// closure owns it.
    struct Recipe
    {
        vector<Donor> donors;
        vector<RecipeMember> members;
        Integer rhs;
        size_t state_budget;
        InferredCumulativeMutation mutation;
        shared_ptr<map<vector<size_t>, optional<LiftedCoverCut>>> programmes;
        shared_ptr<InferredCumulativeStats> stats;
    };
}

InferredCumulative::InferredCumulative(shared_ptr<InferredCumulativeStats> stats) :
    _stats(move(stats)), _max_covers(100), _max_posted(5), _maximum_capacity(1000), _max_lifting_calls(20000), _max_programme_states(100000),
    // Energy only: a valid cut holds at every 0/1 point the donor's row allows,
    // so no time-tabling verdict about a single time point can differ.
    _rules(CumulativeRules{.time_table = false, .overload = true, .profile_overload = true}), _mutation(inferred_cumulative_mutation::None{})
{
}

auto InferredCumulative::with_budgets(size_t max_covers, size_t max_posted) -> InferredCumulative &
{
    _max_covers = max_covers;
    _max_posted = max_posted;
    return *this;
}

auto InferredCumulative::with_maximum_capacity(size_t capacity) -> InferredCumulative &
{
    _maximum_capacity = capacity;
    return *this;
}

auto InferredCumulative::with_lifting_call_budget(size_t calls) -> InferredCumulative &
{
    _max_lifting_calls = calls;
    return *this;
}

auto InferredCumulative::with_programme_state_budget(size_t states) -> InferredCumulative &
{
    _max_programme_states = states;
    return *this;
}

auto InferredCumulative::with_rules(CumulativeRules rules) -> InferredCumulative &
{
    _rules = rules;
    return *this;
}

auto InferredCumulative::with_proof_mutation(InferredCumulativeMutation mutation) -> InferredCumulative &
{
    _mutation = mutation;
    return *this;
}

auto InferredCumulative::with_makespan(IntegerVariableID makespan) -> InferredCumulative &
{
    _makespan = makespan;
    return *this;
}

auto InferredCumulative::run(Problem & problem, Propagators & propagators, State & state, ProofLogger * const logger) -> bool
{
    auto bump = [&](size_t InferredCumulativeStats::* field, size_t by = 1) {
        if (_stats)
            (*_stats).*field += by;
    };

    // What the model says about the makespan, if the caller named one: the rows
    // saying each task finishes by it, which are what a bound on it is derived
    // from. Looked up once rather than per cut.
    map<IntegerVariableID, makespan_energy::MakespanLink> makespan_links;
    if (_makespan)
        makespan_links = find_makespan_links(problem, logger, *_makespan);

    // One pass over every posted Cumulative rather than one pass each, because
    // Equation 4's lifting subproblem is over all of them at once. Everything
    // downstream --- the cover budget, the visited rule, the subproblem budget,
    // and how many constraints are posted --- is then global, which is what the
    // reference implementation does with its single matrix.
    vector<Donor> donors;
    vector<Task> tasks;
    map<pair<IntegerVariableID, Integer>, size_t> task_of;

    for (const auto & donor : problem.each_constraint_of_type<Cumulative>()) {
        bump(&InferredCumulativeStats::donors_seen);

        // The mechanism no longer minds an optional donor --- a presence is a
        // conjunct of the activity flag, so the rows this argues over are the
        // same shape, and install_derived_cumulative carries the literal into
        // the reasons. What is still open here is the *cross-donor* half: this
        // presolver draws tasks from several Cumulatives and bridges one
        // donor's flags to another's, and two donors' activity flags cancel
        // against each other only if their presence conjuncts do too. Declined
        // until that has a rule of its own rather than a hopeful `pol`.
        if (! donor.presences().empty()) {
            bump(&InferredCumulativeStats::declined_optional);
            if (logger)
                logger->emit_proof_comment("presolve lifted cover: declining " + as_string(donor.constraint_id()) + ", optional tasks");
            continue;
        }

        // What of this donor a cut can be lifted out of: its capacity as a
        // number, and the tasks whose length and height are the constants its
        // rows put on them. A task with a variable one is set aside rather than
        // costing the whole donor its column in the matrix --- it takes no part
        // in any cover, and its terms come out of every row first.
        auto view = cumulative_donor_view(donor, state);
        if (! view) {
            bump(&InferredCumulativeStats::declined_variable_arguments);
            if (logger)
                logger->emit_proof_comment("presolve lifted cover: declining " + as_string(donor.constraint_id()) + ", capacity is not reducible");
            continue;
        }
        if (! view->set_aside.empty())
            bump(&InferredCumulativeStats::donors_with_set_aside_tasks);

        const auto & starts = donor.starts();
        auto capacity = view->capacity;

        auto which = donors.size();
        donors.push_back(Donor{donor.constraint_id(), starts.size(), capacity, *view});

        // Every task already found needs a slot for the donor just added,
        // whether or not it turns out to appear in it --- and before the loop
        // below, which is what fills those slots in.
        for (auto & task : tasks) {
            task.demands.resize(donors.size(), 0_i);
            task.positions.resize(donors.size(), std::nullopt);
        }

        for (auto i : view->usable) {
            auto length = view->lengths[i];
            auto demand = view->heights[i];
            // A task that alone exceeds the capacity can never run at all --- the
            // donor's own row says so, and including it would pad every cover it
            // touched. That is this *donor* having nothing to say about it, and
            // another may still have.
            if (demand > capacity)
                continue;

            // Matched across donors by start and length, and a donor's second
            // task with the same pair stays its own column rather than being
            // merged into the first.
            auto key = pair{starts[i], length};
            auto found = task_of.find(key);
            if (found != task_of.end() && ! tasks[found->second].positions[which]) {
                tasks[found->second].demands[which] = demand;
                tasks[found->second].positions[which] = i;
                continue;
            }

            auto [s_lo, s_hi] = state.bounds(starts[i]);
            Task task{starts[i], length, s_lo, s_hi + length - 1_i, vector<Integer>(donors.size(), 0_i),
                vector<optional<size_t>>(donors.size(), std::nullopt), which};
            task.demands[which] = demand;
            task.positions[which] = i;
            task_of.emplace(key, tasks.size());
            tasks.push_back(move(task));
        }
    }

    bump(&InferredCumulativeStats::tasks, tasks.size());
    if (donors.empty() || tasks.size() < 2)
        return true;

    vector<Integer> capacities, durations;
    for (const auto & donor : donors)
        capacities.push_back(donor.capacity);
    for (const auto & task : tasks)
        durations.push_back(task.length);

    vector<vector<Integer>> demands(donors.size());
    for (size_t row = 0; row < donors.size(); ++row)
        for (const auto & task : tasks)
            demands[row].push_back(task.demands[row]);

    // Algorithm 1, per resource, and then merged: the covers a resource can
    // offer are its own, but which of them are worth lifting is decided across
    // all of them, as `collect_cover_sets` does. Covers of more than three tasks
    // survive the budget outright, since nothing else produces them.
    vector<vector<size_t>> covers;
    {
        set<vector<size_t>> seen;
        vector<vector<size_t>> pooled;
        for (size_t row = 0; row < donors.size(); ++row)
            for (auto & cover : collect_covers(tasks, demands[row], capacities[row], _max_covers, _maximum_capacity + 1))
                if (seen.insert(cover).second)
                    pooled.push_back(move(cover));

        auto bound_of = [&](const vector<size_t> & cover) {
            auto total = 0_i;
            for (auto i : cover)
                total += tasks[i].length;
            return pair{total, Integer{static_cast<long long>(cover.size()) - 1}};
        };
        std::sort(pooled.begin(), pooled.end(), [&](const vector<size_t> & a, const vector<size_t> & b) {
            auto [ta, ra] = bound_of(a);
            auto [tb, rb] = bound_of(b);
            if (ta * rb != tb * ra)
                return ta * rb > tb * ra;
            return a < b;
        });

        // `[c for c in covers if len(c) > 3] + covers[:pool_size]`: every cover
        // of more than three tasks survives outright, since nothing but the
        // equal-demand families produces one, and then the best `max_covers`
        // overall whatever their size. So the budget bites twice --- once on
        // each resource's short families, and again across all of them.
        set<vector<size_t>> taken;
        for (const auto & cover : pooled)
            if (cover.size() > 3 && taken.insert(cover).second)
                covers.push_back(cover);
        for (size_t i = 0; i < pooled.size() && i < _max_covers; ++i)
            if (taken.insert(pooled[i]).second)
                covers.push_back(pooled[i]);
    }

    // Algorithm 2: lift each cover, skipping any whose support a previous
    // lifting already established, and keeping the best `_max_posted` by
    // capacity bound. Nothing here asks whether a constraint can be *proved* ---
    // that comes after, so the gap between what the published method infers and
    // what we can certify is a number rather than a design decision.
    vector<Cut> cuts;
    vector<pair<set<size_t>, size_t>> visited;
    auto calls_left = _max_lifting_calls;

    for (const auto & cover : covers) {
        bump(&InferredCumulativeStats::covers_considered);

        // Example 12: a cover already inside the support of something lifted
        // earlier will re-derive it, so the subproblems are wasted.
        auto already = false;
        for (const auto & [support, cardinality] : visited)
            if (cardinality <= cover.size() && std::includes(support.begin(), support.end(), cover.begin(), cover.end())) {
                already = true;
                break;
            }
        if (already) {
            bump(&InferredCumulativeStats::dropped_visited);
            continue;
        }

        if (calls_left == 0)
            break;
        auto lifted = lift_cover(tasks, demands, capacities, cover, calls_left, _max_programme_states);
        calls_left -= lifted.subproblems;
        bump(&InferredCumulativeStats::lifting_subproblems, lifted.subproblems);
        bump(&InferredCumulativeStats::lifting_subproblems_over_budget, lifted.over_budget);
        if (lifted.rhs < 1_i)
            continue;

        vector<size_t> support;
        for (size_t i = 0; i < tasks.size(); ++i)
            if (lifted.coefficients[i] > 0_i)
                support.push_back(i);
        if (support.size() < 2)
            continue;

        set<size_t> unit;
        for (size_t i = 0; i < tasks.size(); ++i)
            if (lifted.coefficients[i] == 1_i)
                unit.insert(i);
        visited.emplace_back(move(unit), cover.size());

        // Dominance: a constraint some model row already implies term by term
        // says nothing new.
        auto dominated = false;
        for (size_t row = 0; row < donors.size() && ! dominated; ++row) {
            auto row_dominates = capacities[row] <= lifted.rhs;
            for (size_t i = 0; i < tasks.size() && row_dominates; ++i)
                row_dominates = lifted.coefficients[i] <= demands[row][i];
            dominated = row_dominates;
        }
        if (dominated) {
            bump(&InferredCumulativeStats::dropped_dominated);
            continue;
        }

        Integer energy = 0_i;
        for (auto i : support)
            energy += durations[i] * lifted.coefficients[i];

        vector<Integer> cut_coefficients;
        for (auto i : support)
            cut_coefficients.push_back(lifted.coefficients[i]);
        cuts.push_back(Cut{support, move(cut_coefficients), lifted.rhs, {}, energy});
        bump(&InferredCumulativeStats::cuts_found);
    }

    // Step L5: the best `_max_posted` by capacity bound.
    std::sort(cuts.begin(), cuts.end(), [&](const Cut & a, const Cut & b) {
        if (a.energy * b.rhs != b.energy * a.rhs)
            return a.energy * b.rhs > b.energy * a.rhs;
        return a.support < b.support;
    });
    if (cuts.size() > _max_posted) {
        bump(&InferredCumulativeStats::dropped_over_budget, cuts.size() - _max_posted);
        cuts.erase(cuts.begin() + static_cast<long>(_max_posted), cuts.end());
    }

    // Only now, the part the paper does not have to do: build the dynamic
    // programme that says each cut follows from the rows, which is also its
    // certificate. Algorithm 2 solves its lifting subproblems exactly, so this
    // should accept everything it produced; a constraint it refuses is a
    // constraint the published method inferred and that does not in fact hold,
    // which is dropped and counted rather than asserted.
    vector<Cut> accepted;
    for (auto & cut : cuts) {
        vector<vector<Integer>> support_demands(donors.size());
        for (size_t row = 0; row < donors.size(); ++row)
            for (auto i : cut.support)
                support_demands[row].push_back(demands[row][i]);

        auto validity = validate_lifted_cover_cut(support_demands, cut.coefficients, capacities, cut.rhs, _max_programme_states);
        cut.validated = move(validity.cut);
        if (! cut.validated) {
            bump(validity.over_state_budget ? &InferredCumulativeStats::dropped_over_state_budget : &InferredCumulativeStats::cuts_uncertifiable);
            if (logger)
                logger->emit_proof_comment("presolve lifted cover: dropping an inferred constraint over " + to_string(cut.support.size()) +
                    " tasks, " + (validity.over_state_budget ? "its dynamic programme is over budget" : "it does not follow from the rows"));
            continue;
        }
        accepted.push_back(move(cut));
    }

    for (const auto & cut : accepted) {
        vector<DerivedCumulativeTask> derived_tasks;
        Recipe recipe{.donors = donors,
            .members = {},
            .rhs = cut.rhs,
            .state_budget = _max_programme_states,
            .mutation = _mutation,
            .programmes = make_shared<map<vector<size_t>, optional<LiftedCoverCut>>>(),
            .stats = _stats};
        vector<optional<makespan_energy::MakespanLink>> links;
        for (size_t k = 0; k < cut.support.size(); ++k) {
            const auto & task = tasks[cut.support[k]];
            auto link = makespan_links.find(task.start);
            links.push_back(link == makespan_links.end() ? std::nullopt : optional<makespan_energy::MakespanLink>{link->second});
            derived_tasks.push_back(DerivedCumulativeTask{
                donors[task.canonical_donor].id, *task.positions[task.canonical_donor], task.start, task.length, cut.coefficients[k]});
            recipe.members.push_back(RecipeMember{task.canonical_donor, *task.positions[task.canonical_donor], task.demands, task.positions,
                cut.coefficients[k], task.t_lo, task.t_hi});
        }

        // Every time point in the middle of the window has all of the cut's
        // members present, and its programme is the one discovery already built.
        // Seed it, so only the restrictions at the edges --- where some members
        // have no flags and so no terms in the rows --- have a programme of
        // their own.
        vector<size_t> everyone(recipe.members.size());
        std::iota(everyone.begin(), everyone.end(), size_t{0});
        recipe.programmes->emplace(move(everyone), cut.validated);

        // Only the rows the programme kept are ever cited, and a restriction to
        // fewer members can only make fewer of them bind, so this is every donor
        // whose row could be wanted at any time point.
        vector<ConstraintID> row_donors;
        for (auto row : cut.validated->row_indices)
            row_donors.push_back(donors[row].id);

        DerivedCumulativeSpec spec{.tasks = derived_tasks,
            .capacity = cut.rhs,
            .row_donors = row_donors,
            .recipe = [recipe](ProofLogger & recipe_logger, const DerivedCumulativeRows & rows, Integer t) -> optional<ProofLine> {
                const auto & tracker = recipe_logger.names_and_ids_tracker();

                // Only the members whose window covers `t` have flags, and they
                // are exactly the ones with a term in the rows there. The
                // coefficients cannot move to suit them --- a Cumulative has one
                // height per task --- so the cut is simply restricted, and stays
                // valid because setting an absent task's flag to zero is a point
                // the cut already covered.
                vector<size_t> present;
                vector<ProofFlag> flags;
                vector<Integer> coefficients;
                for (size_t k = 0; k < recipe.members.size(); ++k) {
                    const auto & member = recipe.members[k];
                    if (t < member.t_lo || t > member.t_hi)
                        continue;
                    auto flag = active_flag_for(tracker, recipe.donors[member.canonical_donor].id, member.canonical_position, t);
                    if (! flag)
                        return std::nullopt;
                    present.push_back(k);
                    flags.push_back(*flag);
                    coefficients.push_back(member.coefficient);
                }
                if (present.empty())
                    return std::nullopt;

                vector<vector<Integer>> present_demands(recipe.donors.size());
                vector<Integer> capacities;
                for (size_t row = 0; row < recipe.donors.size(); ++row) {
                    capacities.push_back(recipe.donors[row].capacity);
                    for (auto k : present)
                        present_demands[row].push_back(recipe.members[k].demands[row]);
                }

                // A miss here is a genuine restriction: the row for a time point
                // where every member is present is the programme discovery
                // built, seeded before any of this ran.
                auto cached = recipe.programmes->find(present);
                if (cached == recipe.programmes->end()) {
                    if (recipe.stats)
                        ++recipe.stats->restricted_rows_rebuilt;
                    cached = recipe.programmes
                                 ->emplace(present,
                                     validate_lifted_cover_cut(present_demands, coefficients, capacities, recipe.rhs, recipe.state_budget).cut)
                                 .first;
                }
                if (! cached->second)
                    return std::nullopt;

                auto claimed = coefficients;
                auto claimed_rhs = recipe.rhs;
                auto programme = cached->second;
                auto bridge_wrong_task = std::holds_alternative<inferred_cumulative_mutation::BridgeWrongTask>(recipe.mutation);
                overloaded{//
                    [&](const inferred_cumulative_mutation::None &) {},
                    [&](const inferred_cumulative_mutation::ClaimTighterCapacity &) { claimed_rhs -= 1_i; },
                    [&](const inferred_cumulative_mutation::ClaimTallerTask &) {
                        if (! claimed.empty())
                            claimed[0] += 1_i;
                    },
                    [&](const inferred_cumulative_mutation::ClaimTighterRow &) {
                        auto tighter = capacities;
                        for (auto & capacity : tighter)
                            capacity -= 1_i;
                        programme = validate_lifted_cover_cut(present_demands, coefficients, tighter, recipe.rhs, recipe.state_budget).cut;
                    },
                    // Corrupts the makespan bound rather than the rows, so the
                    // rows are the honest ones.
                    [&](const inferred_cumulative_mutation::ClaimHigherMakespanBound &) {},
                    // Corrupts the crossing, which happens below.
                    [&](const inferred_cumulative_mutation::BridgeWrongTask &) {}}
                    .visit(recipe.mutation);
                // A mutation that leaves nothing to derive has nothing to be
                // rejected either, and a test asserting on it would be asserting
                // that a constraint went missing.
                if (! programme)
                    return std::nullopt;

                // The rows go one level deeper than the caller's, so that the
                // bridges carrying them onto the members' own flags die with the
                // rest of the working: there are three `pol` per member per
                // donor per time point, and at Top none of them would ever be
                // deleted. Only the pin the caller gets back survives.
                auto saved_level = recipe_logger.proof_level();
                recipe_logger.enter_proof_level(saved_level + 1);

                vector<ProofLine> kept_rows;
                vector<vector<ProofFlag>> kept_weaken_out;
                auto give_up = false;
                for (auto row : programme->row_indices) {
                    const auto & donor = recipe.donors[row];
                    auto found_row = rows.find(donor.id);
                    if (found_row == rows.end()) {
                        give_up = true;
                        break;
                    }

                    // Reduced to the constant-argument form everything below
                    // lifts out of: this donor's set-aside tasks weakened away,
                    // and a variable capacity replaced by the number
                    // `donor.capacity` already holds.
                    auto line = recover_constant_argument_row(recipe_logger, donor.view, donor.id, found_row->second, t, ProofLevel::Temporary);
                    if (! line) {
                        give_up = true;
                        break;
                    }

                    // Which of the present members this row actually speaks
                    // about, and where they sit in it.
                    vector<BridgedRowTerm> terms;
                    set<size_t> in_the_row;
                    auto missing = false;
                    for (size_t j = 0; j < present.size() && ! missing; ++j) {
                        const auto & member = recipe.members[present[j]];
                        if (member.demands[row] <= 0_i)
                            continue;
                        auto position = member.positions[row];
                        if (! position) {
                            missing = true;
                            break;
                        }
                        in_the_row.insert(*position);

                        // Nothing to carry when the row already speaks in the
                        // member's own flags, which is the whole of the
                        // single-resource case.
                        optional<ProofLine> bridge;
                        if (member.canonical_donor != row) {
                            // Whose flag this term is carried onto. Honestly its
                            // own; under the mutation, the member before it, so
                            // that the row ends up saying something about a
                            // different task from the one it is spending its
                            // capacity on.
                            auto onto = j;
                            if (bridge_wrong_task && j > 0)
                                onto = j - 1;
                            const auto & carried = recipe.members[present[onto]];

                            auto theirs = active_flag_for(tracker, donor.id, *position, t);
                            auto their_conjuncts = active_conjuncts_for(tracker, donor.id, *position, t);
                            auto our_conjuncts =
                                active_conjuncts_for(tracker, recipe.donors[carried.canonical_donor].id, carried.canonical_position, t);
                            if (! theirs || ! their_conjuncts || ! our_conjuncts) {
                                missing = true;
                                break;
                            }
                            bridge = recover_conjunction_flag_bridge(
                                recipe_logger, flags[onto], *our_conjuncts, *theirs, *their_conjuncts, ProofLevel::Temporary);
                            terms.push_back(BridgedRowTerm{member.demands[row], flags[onto], bridge});
                            continue;
                        }
                        terms.push_back(BridgedRowTerm{member.demands[row], flags[j], bridge});
                    }

                    if (missing || terms.empty()) {
                        give_up = true;
                        break;
                    }

                    // Everything else of this donor's that could be running now
                    // has to come out of the row. Over every position, not up to
                    // the first one without flags: a task outside its window has
                    // neither a term nor a flag, and stopping there would leave
                    // the later tasks' terms in.
                    vector<ProofFlag> weaken_out;
                    for (auto position : donor.view.usable) {
                        if (in_the_row.contains(position))
                            continue;
                        if (auto flag = active_flag_for(tracker, donor.id, position, t))
                            weaken_out.push_back(*flag);
                    }

                    auto bridged = any_of(terms, [](const BridgedRowTerm & term) { return term.implies_row_flag.has_value(); });
                    if (! bridged) {
                        kept_rows.push_back(*line);
                        kept_weaken_out.push_back(move(weaken_out));
                    }
                    else {
                        kept_rows.push_back(recover_bridged_row(recipe_logger, *line, terms, weaken_out, donor.capacity, ProofLevel::Temporary));
                        kept_weaken_out.emplace_back();
                    }
                }

                optional<ProofLine> result;
                if (! give_up)
                    result =
                        derive_lifted_cover_cut(recipe_logger, kept_rows, *programme, flags, claimed, kept_weaken_out, claimed_rhs, ProofLevel::Top);

                recipe_logger.enter_proof_level(saved_level);
                recipe_logger.forget_proof_level(saved_level + 2);
                return result;
            },
            .makespan = _makespan,
            .makespan_links = links,
            .makespan_bound_reached =
                [stats = _stats](Integer bound) {
                    if (stats && bound > stats->certified_makespan_bound)
                        stats->certified_makespan_bound = bound;
                },
            .makespan_mutation = std::holds_alternative<inferred_cumulative_mutation::ClaimHigherMakespanBound>(_mutation)
                ? makespan_energy::MakespanEnergyMutation{makespan_energy::makespan_energy_mutation::ClaimHigherBound{}}
                : makespan_energy::MakespanEnergyMutation{makespan_energy::makespan_energy_mutation::None{}},
            .rules = _rules};

        if (! install_derived_cumulative(propagators, state, logger, move(spec))) {
            bump(&InferredCumulativeStats::declined_by_install);
            continue;
        }

        bump(&InferredCumulativeStats::cuts_posted);
        if (*std::max_element(cut.coefficients.begin(), cut.coefficients.end()) > 1_i)
            bump(&InferredCumulativeStats::non_unit_cuts_posted);
        if (cut.validated->row_indices.size() > 1)
            bump(&InferredCumulativeStats::multi_resource_cuts_posted);
        if (_stats && cut.bound() > _stats->largest_capacity_bound)
            _stats->largest_capacity_bound = cut.bound();
        if (logger)
            logger->emit_proof_comment("presolve lifted cover: inferred a cut over " + to_string(cut.support.size()) + " tasks on " +
                to_string(cut.validated->row_indices.size()) + " resources with capacity " + to_string(cut.rhs.raw_value) + ", makespan bound " +
                to_string(cut.bound().raw_value));
    }

    return true;
}

auto InferredCumulative::clone() const -> unique_ptr<Presolver>
{
    auto result = make_unique<InferredCumulative>(_stats);
    result->with_budgets(_max_covers, _max_posted);
    result->with_maximum_capacity(_maximum_capacity);
    result->with_lifting_call_budget(_max_lifting_calls);
    result->with_programme_state_budget(_max_programme_states);
    result->with_rules(_rules);
    result->with_proof_mutation(_mutation);
    if (_makespan)
        result->with_makespan(*_makespan);
    return result;
}
