#include <gcs/constraints/innards/makespan_energy.hh>
#include <gcs/constraints/innards/window_energy.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_logger.hh>

#include <algorithm>
#include <iterator>
#include <string>
#include <utility>
#include <variant>
#include <vector>

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::innards::makespan_energy;

using std::max;
using std::min;
using std::nullopt;
using std::optional;
using std::size_t;
using std::to_string;
using std::vector;

namespace
{
    /// How many time points in `[from, to)` the constraint has a capacity row
    /// for. Clamped at both ends, so a window reaching past the last row counts
    /// what is there rather than reading off the end of the prefix sums.
    [[nodiscard]] auto slots_within(const vector<Integer> & prefix, Integer lo, Integer from, Integer to) -> Integer
    {
        auto at = [&](Integer t) {
            auto idx = (t - lo).raw_value;
            return prefix[static_cast<size_t>(max(0LL, min(idx, static_cast<long long>(prefix.size()) - 1)))];
        };
        return at(to) - at(from);
    }

    /// Where a task's start can be, given a makespan of `hi`. With a link, the
    /// model's row puts it at `hi - bound` whatever the task's own domain says,
    /// which is where the deadline enters the arithmetic; without one, the
    /// domain is all there is.
    [[nodiscard]] auto start_bounds_within(const EnergyTask & task, Integer hi) -> std::pair<Integer, Integer>
    {
        return {task.start_lb, task.link ? min(task.start_ub, hi - task.link->bound) : task.start_ub};
    }

    /// The activity the window-energy lemma can certify for one task inside
    /// `[lo, hi)`.
    [[nodiscard]] auto energy_within(const EnergyTask & task, Integer lo, Integer hi) -> Integer
    {
        auto flags_size = static_cast<size_t>(max(0LL, (task.t_hi - task.t_lo + 1_i).raw_value));
        return window_energy::window_energy_bound(task.length, task.t_lo, flags_size, lo, hi, start_bounds_within(task, hi));
    }
}

auto gcs::innards::makespan_energy::makespan_energy_bound(const vector<EnergyTask> & tasks, Integer capacity,
    const vector<Integer> & time_slot_prefix, Integer time_slot_lo, Integer known_bound, Integer search_up_to) -> optional<MakespanBound>
{
    if (tasks.empty() || capacity <= 0_i || time_slot_prefix.size() < 2)
        return nullopt;

    // Where the argument starts. Anything earlier has no capacity row to cite
    // and no task that could be running, so counting it would be supply the
    // tasks cannot draw on --- and every unit of it costs a unit of the bound.
    auto lo = time_slot_lo;
    auto last = lo + Integer(static_cast<long long>(time_slot_prefix.size()) - 1);

    optional<MakespanBound> best;
    for (Integer mu = lo; mu <= min(search_up_to, last); ++mu) {
        if (mu + 1_i <= known_bound)
            continue;

        Integer energy = 0_i;
        for (const auto & task : tasks)
            energy += task.height * energy_within(task, lo, mu);

        auto supply = capacity * slots_within(time_slot_prefix, lo, lo, mu);
        if (energy > supply)
            best = MakespanBound{
                mu + 1_i, lo, mu, energy, supply, slots_within(time_slot_prefix, lo, lo, mu + 1_i) > slots_within(time_slot_prefix, lo, lo, mu)};
    }

    return best;
}

auto gcs::innards::makespan_energy::derive_makespan_bound(ProofLogger & logger, const ReasonLiterals & reason, IntegerVariableID makespan,
    const vector<EnergyTask> & tasks, const std::map<Integer, ProofLine> & capacity_rows, const MakespanBound & bound,
    MakespanEnergyMutation mutation, ProofLevel level) -> void
{
    auto claim_higher = std::holds_alternative<makespan_energy_mutation::ClaimHigherBound>(mutation);
    auto omit_row = std::holds_alternative<makespan_energy_mutation::OmitCapacityRow>(mutation);
    auto forget_deadline = std::holds_alternative<makespan_energy_mutation::ForgetTheDeadline>(mutation);

    // Under ClaimHigherBound the caller infers one more than the argument
    // reaches, and the window widens to match --- but only where widening
    // brings another capacity row with it. Where it does not, the honest
    // window and the corrupted conclusion are already a unit apart, and moving
    // it would only be arguing about a deadline nothing else changed.
    auto hi = claim_higher && bound.wider_supplies_more ? bound.hi + 1_i : bound.hi;

    // Recomputed at the window actually argued over rather than copied from
    // `bound`, so that a mutation's comment says what the mutation did.
    Integer energy_here = 0_i;
    for (const auto & task : tasks)
        energy_here += task.height * energy_within(task, bound.lo, hi);
    auto rows_here = std::distance(capacity_rows.begin(), capacity_rows.lower_bound(hi));
    logger.emit_proof_comment("makespan energy: over [" + to_string(bound.lo.raw_value) + "," + to_string(hi.raw_value) + ") the tasks need " +
        to_string(energy_here.raw_value) + " out of " + to_string(rows_here) + " time points of the resource");

    // The context every step below runs under: the caller's reason, plus the
    // negated conclusion, which is what confines each task to the window.
    ReasonLiterals deadline{reason};
    deadline.push_back(makespan < hi + 1_i);

    PolBuilder pol;
    for (const auto & [t, line] : capacity_rows) {
        if (t >= hi)
            break;
        if (omit_row && t == hi - 1_i)
            continue;
        pol.add(line);
    }

    for (const auto & task : tasks) {
        if (! task.before || ! task.after || ! task.active)
            throw ProofError{"makespan energy bound: a task has no activity flags to argue over"};
        // The search clipped the lemma's window using t_lo and t_hi, and the
        // lemma will clip it using the flag range. A disagreement would make
        // the bound the caller is about to claim one the derivation does not
        // reach, which VeriPB would only notice as a rejected wrapping RUP.
        if (task.active->size() != static_cast<size_t>(max(0LL, (task.t_hi - task.t_lo + 1_i).raw_value)))
            throw ProofError{"makespan energy bound: a task's flag range is not the window the bound was searched over"};

        // The deadline, made available to the lemma's own reverse unit
        // propagation. Its end-of-window literals say `start <= hi - bound`,
        // which follows from the model's `makespan - start >= bound` and the
        // negated conclusion, and from nothing a checker finds on its own:
        // reverse unit propagation will not carry a bound from one variable's
        // bits to another's across a linear row. Adding that row to the two
        // order literals' own definitions cancels both variables' bits exactly
        // and leaves the clause `~[start >= v] \/ [makespan >= hi + 1]`, which
        // the lemma's RUPs then resolve against, one order literal at a time.
        // Only where the task's own domain does not already confine it: the
        // lemma asks for `start < v` at `v` above what it was given as an upper
        // bound, and where that bound is the domain's, the reason alone RUPs it.
        if (task.link && ! forget_deadline && task.start_ub > hi - task.link->bound) {
            if (! task.link->row)
                throw ProofError{"makespan energy bound: a task's makespan link has no row to cite"};
            PolBuilder confine;
            confine.add(*task.link->row);
            confine.add_for_literal(logger.names_and_ids_tracker(), task.start >= hi - task.link->bound + 1_i);
            confine.add_for_literal(logger.names_and_ids_tracker(), makespan < hi + 1_i);
            confine.saturate();
            confine.emit(logger, level);
        }

        window_energy::ConstantLengthTask lemma_task{task.start, task.length, task.t_lo, *task.before, *task.after, *task.active};
        auto energy = window_energy::derive_window_energy(
            logger, forget_deadline ? reason : deadline, lemma_task, bound.lo, hi, start_bounds_within(task, hi), level);

        // A task the window leaves no room for contributes nothing, which is a
        // weaker argument rather than a wrong one: the bound search counted the
        // same zero.
        if (! energy)
            continue;
        if (energy->bound != energy_within(task, bound.lo, hi))
            throw ProofError{"makespan energy bound: window energy derivation is weaker than the bound assumed"};
        pol.add(energy->line, task.height);
    }

    pol.emit(logger, level);
}
