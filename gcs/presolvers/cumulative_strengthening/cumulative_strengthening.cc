#include <gcs/constraint_id.hh>
#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/cumulative/derived_cumulative.hh>
#include <gcs/exception.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
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

using std::make_unique;
using std::map;
using std::max;
using std::move;
using std::optional;
using std::shared_ptr;
using std::size_t;
using std::to_string;
using std::unique_ptr;
using std::vector;

namespace
{
    /// The donor's arguments, once every one of them has been confirmed
    /// constant. A variable length, height or capacity is a v1 restriction:
    /// with a variable height the donor's row is over bit-linearised
    /// contribution flags rather than `height * active`, so a subset sum of the
    /// heights is not what the row's coefficients are.
    struct ConstantTaskData
    {
        vector<Integer> lengths, heights;
        Integer capacity;
    };

    [[nodiscard]] auto constant_task_data(const Cumulative & donor) -> optional<ConstantTaskData>
    {
        ConstantTaskData data{{}, {}, 0_i};

        auto value_of = [](const IntegerVariableID & v) -> optional<Integer> {
            if (! is_constant_variable(v))
                return std::nullopt;
            return std::get<ConstantIntegerVariableID>(v).const_value;
        };

        auto capacity = value_of(donor.capacity());
        if (! capacity)
            return std::nullopt;
        data.capacity = *capacity;

        for (const auto & l : donor.lengths()) {
            auto length = value_of(l);
            if (! length)
                return std::nullopt;
            data.lengths.push_back(*length);
        }

        for (const auto & h : donor.heights()) {
            auto height = value_of(h);
            if (! height)
                return std::nullopt;
            data.heights.push_back(*height);
        }

        return data;
    }

    /// What the presolver worked out for one time point: the heights of the
    /// tasks that can be running then, and the largest load they can actually
    /// reach without exceeding the capacity.
    struct TimePoint
    {
        Integer t;
        vector<size_t> tasks;
        vector<Integer> heights;
        Integer kappa;
        /// Whether derive_subset_sum_strengthening() will take its two-step
        /// divisibility path here, predicted by the same test it applies. Only
        /// the other path costs anything worth budgeting for.
        bool by_division;
    };
}

CumulativeStrengthening::CumulativeStrengthening(shared_ptr<CumulativeStrengtheningStats> stats) :
    _stats(move(stats)), _max_dynamic_programming_states(20000),
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

        // A derived Cumulative over an optional donor would need the donor's
        // presence literals in every reason it gives, which DerivedCumulativeSpec
        // says it does not have. Loudly, because a model that turned optional
        // would otherwise just quietly stop being strengthened.
        if (! donor.presences().empty()) {
            bump(&CumulativeStrengtheningStats::declined_optional);
            if (logger)
                logger->emit_proof_comment("presolve cumulative: declining " + as_string(donor.constraint_id()) + ", optional tasks");
            continue;
        }

        auto data = constant_task_data(donor);
        if (! data) {
            bump(&CumulativeStrengtheningStats::declined_variable_arguments);
            if (logger)
                logger->emit_proof_comment("presolve cumulative: declining " + as_string(donor.constraint_id()) + ", non-constant arguments");
            continue;
        }

        const auto & starts = donor.starts();
        auto n = starts.size();
        auto capacity = data->capacity;

        // The same windowing install_derived_cumulative resolves, and the same
        // windowing the donor encoded: a task can be active from its earliest
        // start to its latest finish. This is the paper's `t in [est_j, lct_j)`.
        vector<Integer> t_lo(n, 0_i), t_hi(n, 0_i);
        vector<size_t> active_tasks;
        for (size_t i = 0; i < n; ++i) {
            if (data->lengths[i] <= 0_i || data->heights[i] <= 0_i)
                continue;
            active_tasks.push_back(i);
            auto [s_lo, s_hi] = state.bounds(starts[i]);
            t_lo[i] = s_lo;
            t_hi[i] = s_hi + data->lengths[i] - 1_i;
        }

        if (active_tasks.empty()) {
            bump(&CumulativeStrengtheningStats::declined_nothing_to_gain);
            continue;
        }

        // A height above the capacity means the donor is infeasible on its own,
        // which is the donor's business to detect and not something to build a
        // subset sum over.
        if (std::any_of(active_tasks.begin(), active_tasks.end(), [&](size_t i) { return data->heights[i] > capacity; })) {
            bump(&CumulativeStrengtheningStats::declined_nothing_to_gain);
            continue;
        }

        auto global_lo = t_lo[active_tasks.front()], global_hi = t_hi[active_tasks.front()];
        for (auto i : active_tasks) {
            global_lo = std::min(global_lo, t_lo[i]);
            global_hi = max(global_hi, t_hi[i]);
        }

        vector<TimePoint> time_points;
        auto kappa = 0_i;
        for (Integer t = global_lo; t <= global_hi; ++t) {
            TimePoint point{t, {}, {}, 0_i, false};
            for (auto i : active_tasks)
                if (t >= t_lo[i] && t <= t_hi[i]) {
                    point.tasks.push_back(i);
                    point.heights.push_back(data->heights[i]);
                }

            // No task can be active here, so the donor wrote no row and there is
            // nothing to derive from.
            if (point.tasks.empty())
                continue;

            point.kappa = largest_subset_sum_at_most(point.heights, capacity);

            auto divisor = 0_i;
            for (const auto & h : point.heights)
                divisor = Integer{std::gcd(divisor.raw_value, h.raw_value)};
            point.by_division = (divisor > 1_i && divisor * (capacity / divisor) == point.kappa);

            kappa = max(kappa, point.kappa);
            time_points.push_back(move(point));
        }

        // kappa is the largest load reachable at any one time point, so it is
        // what the capacity really is. If that is the capacity already, the
        // donor was posted with a number the heights can reach and there is
        // nothing here.
        if (kappa >= capacity) {
            bump(&CumulativeStrengtheningStats::declined_nothing_to_gain);
            continue;
        }

        // Budget the expensive derivation. The dynamic program has a state per
        // reachable partial sum per item, so `items * capacity` bounds it; the
        // divisibility path is two `pol` steps and needs no budgeting. Only
        // relevant with proofs on, since with them off no derivation happens.
        if (logger) {
            long long states = 0;
            for (const auto & point : time_points)
                if (! point.by_division)
                    states += static_cast<long long>(point.heights.size()) * (capacity.raw_value + 1);

            if (states > _max_dynamic_programming_states) {
                bump(&CumulativeStrengtheningStats::declined_over_budget);
                logger->emit_proof_comment("presolve cumulative: declining " + as_string(donor.constraint_id()) + ", derivation would need " +
                    to_string(states) + " dynamic programming states against a budget of " + to_string(_max_dynamic_programming_states));
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
        auto heights = data->heights;
        auto stats = _stats;

        // Fixed for the whole donor, so worked out once rather than per row.
        SubsetSumMutation subset_sum_corruption = std::visit(
            overloaded{//
                [](const cumulative_strengthening_mutation::None &) -> SubsetSumMutation { return subset_sum_mutation::None{}; },
                [](const cumulative_strengthening_mutation::ClaimOneBetter &) -> SubsetSumMutation { return subset_sum_mutation::ClaimOneBetter{}; },
                [](const cumulative_strengthening_mutation::BogusDivisor &) -> SubsetSumMutation { return subset_sum_mutation::BogusDivisor{}; }},
            _mutation);

        DerivedCumulativeSpec spec{.tasks = derived_cumulative_tasks_from(donor_id, starts, data->lengths, heights),
            .capacity = kappa,
            .row_donors = {donor_id},
            .recipe = [donor_id, heights, capacity, kappa, by_time, stats, subset_sum_corruption](
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
                auto donor_row = donor_row_at->second;

                vector<SubsetSumItem> items;
                for (auto i : point->second.tasks) {
                    auto active = recipe_logger.names_and_ids_tracker().find_proof_flag_values(
                        donor_id, ConstraintProofModelData<Cumulative>::active_flag_key(i, t));
                    if (! active)
                        throw ProofError{"cumulative strengthening: the donor has no active flag for task " + to_string(i) + " at time " +
                            to_string(t.raw_value) + ", which install_derived_cumulative should already have declined over"};
                    items.push_back(SubsetSumItem{heights[i], *active});
                }

                recipe_logger.emit_proof_comment(point->second.by_division ? "presolve cumulative gcd" : "presolve cumulative kappa");

                auto strengthened =
                    derive_subset_sum_strengthening(recipe_logger, items, donor_row, capacity, ProofLevel::Top, subset_sum_corruption);

                if (stats) {
                    if (strengthened.by_division)
                        ++stats->rows_by_division;
                    else
                        ++stats->rows_by_dynamic_programming;
                }

                // Land every row on the capacity the derived constraint was
                // declared with, whatever this time point's own largest load
                // was. Two things come of insisting on that rather than handing
                // back a row that merely happens to be no weaker. The rows are
                // then uniform, so the propagator's `pol`s cancel against a
                // known degree; and the step is an implication check, which is
                // syntactic, so it is the one thing that notices a derivation
                // landing somewhere other than where it claimed --- a divisor
                // that does not divide every height still divides *soundly*,
                // and nothing else in the proof would object.
                WPBSum load;
                for (const auto & item : items)
                    load += item.coefficient * std::get<ProofFlag>(item.term);
                return recipe_logger.emit(ImpliesProofRule{strengthened.line}, move(load) <= kappa, ProofLevel::Top);
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
                to_string(capacity.raw_value) + " to " + to_string(kappa.raw_value));

        bump(&CumulativeStrengtheningStats::donors_strengthened);
        if (_stats)
            _stats->capacity_units_removed += capacity - kappa;
    }

    return true;
}

auto CumulativeStrengthening::clone() const -> unique_ptr<Presolver>
{
    auto result = make_unique<CumulativeStrengthening>(_stats);
    result->with_dynamic_programming_budget(_max_dynamic_programming_states);
    result->with_rules(_rules);
    result->with_proof_mutation(_mutation);
    return result;
}
