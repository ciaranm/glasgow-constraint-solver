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

    /// Covers of a donor's tasks, biggest demands first: start at each task in
    /// turn and take the next-biggest until the capacity is overshot, then drop
    /// anything whose removal leaves it still overshooting.
    ///
    /// Starting further down the list is what produces a cover of *small* tasks,
    /// and that is where the interesting cuts come from: a big task lifted into
    /// such a cover takes a coefficient above one, which is the whole gain over
    /// the capacity-one stage before this one.
    [[nodiscard]] auto candidate_covers(const vector<Task> & tasks, Integer capacity, size_t max_covers) -> vector<vector<size_t>>
    {
        vector<size_t> by_demand(tasks.size());
        std::iota(by_demand.begin(), by_demand.end(), size_t{0});
        std::sort(by_demand.begin(), by_demand.end(), [&](size_t a, size_t b) {
            if (tasks[a].demand != tasks[b].demand)
                return tasks[a].demand > tasks[b].demand;
            return a < b;
        });

        auto total = [&](const vector<size_t> & set) {
            return std::accumulate(set.begin(), set.end(), 0_i, [&](Integer a, size_t i) { return a + tasks[i].demand; });
        };

        set<vector<size_t>> seen;
        vector<vector<size_t>> covers;
        for (size_t start = 0; start < by_demand.size() && covers.size() < max_covers; ++start) {
            vector<size_t> cover;
            for (size_t k = start; k < by_demand.size(); ++k) {
                cover.push_back(by_demand[k]);
                if (total(cover) > capacity)
                    break;
            }
            if (total(cover) <= capacity)
                continue;

            // Minimalise from the big end: a cover that still overshoots
            // without its largest member says more about the small ones.
            for (size_t k = 0; k < cover.size();) {
                auto without = cover;
                without.erase(without.begin() + static_cast<long>(k));
                if (without.size() >= 2 && total(without) > capacity)
                    cover = move(without);
                else
                    ++k;
            }

            auto sorted = cover;
            std::sort(sorted.begin(), sorted.end());
            if (seen.insert(sorted).second)
                covers.push_back(move(sorted));
        }
        return covers;
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
    _stats(move(stats)), _max_covers(100), _max_posted(5), _max_support(12),
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

auto InferredCumulative::with_maximum_support(size_t size) -> InferredCumulative &
{
    _max_support = size;
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

    // The planner's exhaustive cover search is over subsets of a cut's support,
    // so the budget it gets has to cover them all or it would refuse time points
    // it could have derived.
    auto planner_budget = _max_support < 20 ? (size_t{1} << _max_support) : size_t{1} << 20;

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

        vector<Cut> cuts;
        for (const auto & cover : candidate_covers(tasks, *capacity, _max_covers)) {
            bump(&InferredCumulativeStats::covers_considered);

            // Forward: run the arithmetic and see what cut comes out, ranking
            // each step by the energy the result can argue about. Nothing here
            // decides what the coefficients ought to be and then goes looking
            // for a derivation --- every candidate weighed is one that derives,
            // so there is no gap between the largest valid coefficient and the
            // largest reachable one to discover by failing.
            auto grown = grow_lifted_cover_cut(demands, durations, *capacity, cover, _max_support);
            if (! grown)
                continue;

            vector<size_t> support;
            for (size_t i = 0; i < tasks.size(); ++i)
                if (grown->coefficients[i] > 0_i)
                    support.push_back(i);
            if (support.size() < 2)
                continue;
            if (support.size() > cover.size())
                bump(&InferredCumulativeStats::lifting_steps, support.size() - cover.size());

            // Is it worth anything? The tasks in the cut need `sum d_i pi_i`
            // units of a resource supplying `rhs`, and the donor's own row over
            // the same tasks needs `sum d_i c_i` of one supplying the capacity.
            // A ratio that does not improve means the row already said it better.
            Integer energy = 0_i, donor_energy = 0_i;
            for (auto i : support) {
                energy += durations[i] * grown->coefficients[i];
                donor_energy += durations[i] * demands[i];
            }
            if (energy * *capacity <= donor_energy * grown->rhs) {
                bump(&InferredCumulativeStats::dropped_no_gain);
                continue;
            }

            // The plan came back indexed by the donor's task positions, and
            // the recipe will replay it against the cut's own members. Remap it
            // once here rather than teaching the emitter about two index
            // spaces.
            vector<Integer> cut_coefficients;
            map<size_t, size_t> member_of;
            for (auto i : support) {
                member_of.emplace(i, cut_coefficients.size());
                cut_coefficients.push_back(grown->coefficients[i]);
            }
            auto remapped = move(grown->plan);
            for (auto & step : remapped) {
                vector<size_t> members;
                for (auto i : step.support)
                    if (auto found = member_of.find(i); found != member_of.end())
                        members.push_back(found->second);
                step.support = move(members);
            }
            cuts.push_back(Cut{support, move(cut_coefficients), grown->rhs, remapped, energy});
            bump(&InferredCumulativeStats::cuts_found);
        }

        // Rank by the makespan bound each carries, and drop anything whose
        // tasks an accepted cut already covers.
        std::sort(cuts.begin(), cuts.end(), [&](const Cut & a, const Cut & b) {
            if (a.bound() != b.bound())
                return a.bound() > b.bound();
            return a.support < b.support;
        });

        vector<Cut> accepted;
        for (auto & cut : cuts) {
            if (accepted.size() >= _max_posted) {
                bump(&InferredCumulativeStats::dropped_over_budget);
                if (logger)
                    logger->emit_proof_comment("presolve lifted cover: a cut beyond the output budget of " + to_string(_max_posted) + " was dropped");
                continue;
            }

            bool subsumed = false;
            for (const auto & already : accepted)
                if (std::includes(already.support.begin(), already.support.end(), cut.support.begin(), cut.support.end())) {
                    subsumed = true;
                    break;
                }
            if (subsumed) {
                bump(&InferredCumulativeStats::dropped_subset);
                continue;
            }

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
    result->with_maximum_support(_max_support);
    result->with_rules(_rules);
    result->with_proof_mutation(_mutation);
    return result;
}
