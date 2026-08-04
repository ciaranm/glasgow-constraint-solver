#include <gcs/constraint_id.hh>
#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/cumulative/derived_cumulative.hh>
#include <gcs/innards/proofs/lifted_cover_cut.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/state.hh>
#include <gcs/presolvers/inferred_cumulative/inferred_cumulative.hh>
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

namespace
{
    /// One task of a donor that could carry a cut.
    struct Task
    {
        size_t position;
        IntegerVariableID start;
        Integer length, demand;
        Integer t_lo, t_hi;
    };

    /// A lifted cover inequality over some of a donor's tasks: `sum_i
    /// coefficients[i] a_i <= rhs`, with `support` indexing into the donor's
    /// task list.
    struct Cut
    {
        vector<size_t> support;
        vector<Integer> coefficients;
        Integer rhs;
        /// The derivation discovery arrived at, over the whole support. Kept
        /// rather than re-found: the row every time point in the middle of the
        /// window needs is this one, and only the restrictions at the edges are
        /// a question the planner has to answer.
        LiftedCoverCutPlan plan;
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
    /// inv_A_longest[a]`), which cannot be what was meant; the paper says
    /// longest and that is what happens here.
    [[nodiscard]] auto collect_covers(const vector<Task> & tasks, Integer capacity, size_t max_covers, size_t cover_cardinality)
        -> vector<vector<size_t>>
    {
        auto n = tasks.size();
        map<Integer, vector<size_t>> by_demand;
        for (size_t i = 0; i < n; ++i)
            by_demand[tasks[i].demand].push_back(i);

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
                if (tasks[x].demand + tasks[y].demand > capacity)
                    remember({x, y});

        if (cover_cardinality >= 3)
            for (size_t x = 0; x < n; ++x)
                for (size_t y = x + 1; y < n; ++y) {
                    auto room = capacity - tasks[x].demand - tasks[y].demand;
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
    /// once `member` is forced to run and has taken its demand off the
    /// capacity. A 0/1 knapsack, by the usual table over residual capacity.
    ///
    /// The paper solves this over *every* resource at once, which is what makes
    /// its lifting cross-resource; this is one row, matching what the
    /// certificate can reach. See issue #673.
    [[nodiscard]] auto lifting_subproblem(
        const vector<Task> & tasks, Integer capacity, const vector<Integer> & coefficients, const vector<size_t> & support, size_t member) -> Integer
    {
        auto residual = capacity - tasks[member].demand;
        if (residual < 0_i)
            return 0_i;

        vector<Integer> best(static_cast<size_t>(residual.raw_value) + 1, 0_i);
        for (auto i : support) {
            if (coefficients[i] <= 0_i)
                continue;
            for (auto room = residual; room >= tasks[i].demand; --room) {
                auto with = best[static_cast<size_t>((room - tasks[i].demand).raw_value)] + coefficients[i];
                auto & here = best[static_cast<size_t>(room.raw_value)];
                here = max(here, with);
            }
        }
        return best[static_cast<size_t>(residual.raw_value)];
    }

    /// Algorithm 2's inner loop: start from the cover inequality
    /// `sum_C x_i <= |C| - 1` and lift every other task into it, longest
    /// duration first, each with the largest coefficient the subproblem allows.
    /// The right-hand side never moves.
    ///
    /// Longest first follows the reference implementation, which sorts by
    /// duration descending; the paper's Algorithm 2 says `arg min d_i`. The
    /// published results came from the code.
    struct Lifted
    {
        vector<Integer> coefficients;
        Integer rhs;
        size_t subproblems;
    };

    [[nodiscard]] auto lift_cover(const vector<Task> & tasks, Integer capacity, const vector<size_t> & cover, size_t budget) -> Lifted
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
        size_t used = 0;
        for (auto member : remaining) {
            if (used >= budget)
                break;
            ++used;
            auto lifted = rhs - lifting_subproblem(tasks, capacity, coefficients, support, member);
            // A negative coefficient would mean the subproblem beat the
            // right-hand side, which cannot happen for a valid inequality; the
            // reference implementation warns about it rather than trusting it.
            if (lifted <= 0_i)
                continue;
            coefficients[member] = lifted;
            support.push_back(member);
        }

        return Lifted{move(coefficients), rhs, used};
    }

    /// Everything the per-time recipe needs, copied out of the presolver so the
    /// closure owns it.
    struct Recipe
    {
        ConstraintID donor;
        size_t donor_size;
        Integer capacity, rhs;
        size_t max_covers;
        InferredCumulativeMutation mutation;
        shared_ptr<map<vector<size_t>, optional<LiftedCoverCutPlan>>> plans;
        shared_ptr<InferredCumulativeStats> stats;

        /// One entry per member of the cut, in the derived constraint's own
        /// task order, filled in by the caller after construction.
        vector<size_t> positions;
        vector<Integer> demands, coefficients, t_lo, t_hi;
    };
}

InferredCumulative::InferredCumulative(shared_ptr<InferredCumulativeStats> stats) :
    _stats(move(stats)), _max_covers(100), _max_posted(5), _maximum_capacity(1000), _max_lifting_calls(20000),
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

auto InferredCumulative::run(Problem & problem, Propagators & propagators, State & state, ProofLogger * const logger) -> bool
{
    auto bump = [&](size_t InferredCumulativeStats::* field, size_t by = 1) {
        if (_stats)
            (*_stats).*field += by;
    };

    // The planner enumerates covers exhaustively while this allows, and falls
    // back to a greedy family beyond it. Lifting makes supports wide, so the
    // fallback is the normal case on a large resource; every drop it causes is
    // a refusal rather than a wrong answer.
    const size_t planner_budget = 4096;

    for (const auto & donor : problem.each_constraint_of_type<Cumulative>()) {
        bump(&InferredCumulativeStats::donors_seen);

        if (! donor.presences().empty()) {
            bump(&InferredCumulativeStats::declined_optional);
            if (logger)
                logger->emit_proof_comment("presolve lifted cover: declining " + as_string(donor.constraint_id()) + ", optional tasks");
            continue;
        }

        auto capacity = constant_value_of(donor.capacity());
        if (! capacity) {
            bump(&InferredCumulativeStats::declined_variable_arguments);
            if (logger)
                logger->emit_proof_comment("presolve lifted cover: declining " + as_string(donor.constraint_id()) + ", variable capacity");
            continue;
        }

        const auto & starts = donor.starts();
        vector<Task> tasks;
        bool constant = true;
        for (size_t i = 0; i < starts.size(); ++i) {
            auto length = constant_value_of(donor.lengths()[i]);
            auto demand = constant_value_of(donor.heights()[i]);
            if (! length || ! demand) {
                constant = false;
                break;
            }
            // A task with nothing to contribute has no term in the row and no
            // flags, and one that alone exceeds the capacity can never run at
            // all --- the donor's own row says so, and including it would pad
            // every cover it touched.
            if (*length <= 0_i || *demand <= 0_i || *demand > *capacity)
                continue;
            auto [s_lo, s_hi] = state.bounds(starts[i]);
            tasks.push_back(Task{i, starts[i], *length, *demand, s_lo, s_hi + *length - 1_i});
        }

        if (! constant) {
            bump(&InferredCumulativeStats::declined_variable_arguments);
            if (logger)
                logger->emit_proof_comment("presolve lifted cover: declining " + as_string(donor.constraint_id()) + ", variable lengths or heights");
            continue;
        }

        bump(&InferredCumulativeStats::tasks, tasks.size());
        if (tasks.size() < 2)
            continue;

        vector<Integer> demands, durations;
        for (const auto & task : tasks) {
            demands.push_back(task.demand);
            durations.push_back(task.length);
        }

        vector<size_t> by_demand(tasks.size());
        std::iota(by_demand.begin(), by_demand.end(), size_t{0});
        std::sort(by_demand.begin(), by_demand.end(), [&](size_t a, size_t b) {
            if (tasks[a].demand != tasks[b].demand)
                return tasks[a].demand > tasks[b].demand;
            return a < b;
        });

        // Algorithm 2: lift each cover, skipping any whose support a previous
        // lifting already established, and keeping the best `_max_posted` by
        // capacity bound. Nothing here asks whether a constraint can be
        // *proved* --- that comes after, so the gap between what the published
        // method infers and what we can certify is a number rather than a
        // design decision.
        vector<Cut> cuts;
        vector<pair<set<size_t>, size_t>> visited;
        auto calls_left = _max_lifting_calls;

        for (const auto & cover : collect_covers(tasks, *capacity, _max_covers, _maximum_capacity + 1)) {
            bump(&InferredCumulativeStats::covers_considered);

            // Example 12: a cover already inside the support of something
            // lifted earlier will re-derive it, so the subproblems are wasted.
            bool already = false;
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
            auto lifted = lift_cover(tasks, *capacity, cover, calls_left);
            calls_left -= lifted.subproblems;
            bump(&InferredCumulativeStats::lifting_subproblems, lifted.subproblems);
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

            // Dominance: a constraint the donor's own row already implies term
            // by term says nothing new.
            bool dominated = true;
            for (size_t i = 0; i < tasks.size() && dominated; ++i)
                if (lifted.coefficients[i] > demands[i])
                    dominated = false;
            if (dominated && *capacity > lifted.rhs)
                dominated = false;
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

        // Only now, the part the paper does not have to do: find a derivation
        // for each. A constraint we cannot derive is dropped and counted --- it
        // is one the published method would have posted and we cannot justify.
        vector<Cut> accepted;
        for (auto & cut : cuts) {
            vector<Integer> support_demands;
            for (auto i : cut.support)
                support_demands.push_back(demands[i]);
            auto plan = plan_lifted_cover_cut(support_demands, cut.coefficients, *capacity, cut.rhs, planner_budget);
            if (! plan) {
                bump(&InferredCumulativeStats::cuts_uncertifiable);
                if (logger)
                    logger->emit_proof_comment("presolve lifted cover: dropping an inferred constraint over " + to_string(cut.support.size()) +
                        " tasks, no derivation found");
                continue;
            }
            cut.plan = move(*plan);
            accepted.push_back(move(cut));
        }

        for (const auto & cut : accepted) {
            vector<DerivedCumulativeTask> derived_tasks;
            Recipe recipe{.donor = donor.constraint_id(),
                .donor_size = starts.size(),
                .capacity = *capacity,
                .rhs = cut.rhs,
                .max_covers = planner_budget,
                .mutation = _mutation,
                .plans = make_shared<map<vector<size_t>, optional<LiftedCoverCutPlan>>>(),
                .stats = _stats,
                .positions = {},
                .demands = {},
                .coefficients = {},
                .t_lo = {},
                .t_hi = {}};
            for (size_t k = 0; k < cut.support.size(); ++k) {
                const auto & task = tasks[cut.support[k]];
                derived_tasks.push_back(DerivedCumulativeTask{recipe.donor, task.position, task.start, task.length, cut.coefficients[k]});
                recipe.positions.push_back(task.position);
                recipe.demands.push_back(task.demand);
                recipe.coefficients.push_back(cut.coefficients[k]);
                recipe.t_lo.push_back(task.t_lo);
                recipe.t_hi.push_back(task.t_hi);
            }

            // Every time point in the middle of the window has all of the cut's
            // members present, and the derivation for that is the one discovery
            // already ran forward. Seed it, so the planner is only ever asked
            // about the restrictions at the edges --- where the coefficients are
            // fixed and the route genuinely has to be searched for.
            vector<size_t> everyone(recipe.positions.size());
            std::iota(everyone.begin(), everyone.end(), size_t{0});
            recipe.plans->emplace(move(everyone), cut.plan);

            DerivedCumulativeSpec spec{.tasks = derived_tasks,
                .capacity = cut.rhs,
                .row_donors = vector<ConstraintID>{recipe.donor},
                .recipe = [recipe](ProofLogger & recipe_logger, const DerivedCumulativeRows & rows, Integer t) -> optional<ProofLine> {
                    const auto & tracker = recipe_logger.names_and_ids_tracker();
                    auto row = rows.find(recipe.donor);
                    if (row == rows.end())
                        return std::nullopt;

                    // Only the members whose window covers `t` have flags, and
                    // they are exactly the ones with a term in the donor's row
                    // there. The coefficients cannot move to suit them --- a
                    // Cumulative has one height per task --- so the cut is
                    // simply restricted, and stays valid because setting an
                    // absent task's flag to zero is a point the cut already
                    // covered.
                    vector<size_t> present;
                    vector<ProofFlag> flags;
                    vector<Integer> demands, coefficients;
                    for (size_t k = 0; k < recipe.positions.size(); ++k) {
                        if (t < recipe.t_lo[k] || t > recipe.t_hi[k])
                            continue;
                        auto flag = active_flag_for(tracker, recipe.donor, recipe.positions[k], t);
                        if (! flag)
                            return std::nullopt;
                        present.push_back(k);
                        flags.push_back(*flag);
                        demands.push_back(recipe.demands[k]);
                        coefficients.push_back(recipe.coefficients[k]);
                    }

                    // Everything else of the donor's that could be running now
                    // has to come out of the row first. Over every position,
                    // not up to the first one without flags: a task outside its
                    // window has neither a term nor a flag, and stopping there
                    // would leave the later tasks' terms in.
                    set<size_t> in_the_cut;
                    for (auto k : present)
                        in_the_cut.insert(recipe.positions[k]);

                    vector<ProofFlag> weaken_out;
                    for (size_t position = 0; position < recipe.donor_size; ++position) {
                        if (in_the_cut.contains(position))
                            continue;
                        if (auto flag = active_flag_for(tracker, recipe.donor, position, t))
                            weaken_out.push_back(*flag);
                    }

                    // A miss here is a genuine restriction: the row for a time
                    // point where every member is present is the plan discovery
                    // grew, seeded before any of this ran.
                    auto cached = recipe.plans->find(present);
                    if (cached == recipe.plans->end()) {
                        if (recipe.stats)
                            ++recipe.stats->restricted_rows_planned;
                        cached = recipe.plans
                                     ->emplace(present, plan_lifted_cover_cut(demands, coefficients, recipe.capacity, recipe.rhs, recipe.max_covers))
                                     .first;
                    }
                    if (! cached->second)
                        return std::nullopt;

                    auto claimed = coefficients;
                    auto claimed_rhs = recipe.rhs;
                    overloaded{//
                        [&](const inferred_cumulative_mutation::None &) {},
                        [&](const inferred_cumulative_mutation::ClaimTighterCapacity &) { claimed_rhs -= 1_i; },
                        [&](const inferred_cumulative_mutation::ClaimTallerTask &) {
                            if (! claimed.empty())
                                claimed[0] += 1_i;
                        },
                        [&](const inferred_cumulative_mutation::SkipAWeakening &) {
                            if (! weaken_out.empty())
                                weaken_out.erase(weaken_out.begin());
                        }}
                        .visit(recipe.mutation);

                    return derive_lifted_cover_cut(
                        recipe_logger, row->second, *cached->second, flags, claimed, weaken_out, claimed_rhs, ProofLevel::Top);
                },
                .rules = _rules};

            if (! install_derived_cumulative(propagators, state, logger, move(spec))) {
                bump(&InferredCumulativeStats::declined_by_install);
                continue;
            }

            bump(&InferredCumulativeStats::cuts_posted);
            if (*std::max_element(cut.coefficients.begin(), cut.coefficients.end()) > 1_i)
                bump(&InferredCumulativeStats::non_unit_cuts_posted);
            if (_stats && cut.bound() > _stats->largest_capacity_bound)
                _stats->largest_capacity_bound = cut.bound();
            if (logger)
                logger->emit_proof_comment("presolve lifted cover: inferred a cut over " + to_string(cut.support.size()) + " tasks with capacity " +
                    to_string(cut.rhs.raw_value) + ", makespan bound " + to_string(cut.bound().raw_value));
        }
    }

    return true;
}

auto InferredCumulative::clone() const -> unique_ptr<Presolver>
{
    auto result = make_unique<InferredCumulative>(_stats);
    result->with_budgets(_max_covers, _max_posted);
    result->with_maximum_capacity(_maximum_capacity);
    result->with_lifting_call_budget(_max_lifting_calls);
    result->with_rules(_rules);
    result->with_proof_mutation(_mutation);
    return result;
}
