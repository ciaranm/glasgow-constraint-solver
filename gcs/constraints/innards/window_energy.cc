#include <gcs/constraints/innards/window_energy.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_logger.hh>

#include <algorithm>
#include <string>
#include <vector>

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::innards::window_energy;

using std::max;
using std::min;
using std::nullopt;
using std::optional;
using std::pair;
using std::size_t;
using std::string;
using std::vector;

namespace
{
    // What the derivation looks like, once the requested window has been
    // clipped to the flag range.
    //
    // Summing the per-time facts
    //
    //     active_t  \/  [s >= t + 1]  \/  ~[s >= t - p + 1]        (t in [a, b))
    //
    // gives a line whose order literals live in two ranges: V = (a, b] for the
    // "starts after t" halves, and U = (a - p, b - p] for the "ends by t" ones.
    // Every value in V n U contributes both [s >= w] and ~[s >= w] to that sum,
    // which is the constant 1, so those cancel inside the pol and the survivors
    // are the P = min(p, b - a) literals of each kind below.
    //
    // What is left is resolved against the start bounds: a `keep` value is one
    // the bounds decide the right way (so a unit RUP under the reason cancels
    // it for free), and a `lose` value one they do not (so the literal axiom
    // cancels it at the cost of one unit of the bound).
    struct Shape
    {
        Integer a, b;       // the clipped window, half-open
        Integer u_lo, u_hi; // U \ V = [u_lo, u_hi], the "ends by t" survivors
        Integer v_lo, v_hi; // V \ U = [v_lo, v_hi], the "starts after t" survivors
        Integer p;          // the task's length
        Integer bound;      // what the derivation establishes
        [[nodiscard]] auto empty() const -> bool
        {
            return b <= a;
        }
    };

    auto shape_of(Integer length, Integer flags_t_lo, size_t flags_size, Integer lo, Integer hi, pair<Integer, Integer> start_bounds) -> Shape
    {
        auto a = max(lo, flags_t_lo), b = min(hi, flags_t_lo + Integer(static_cast<long long>(flags_size)));
        if (b <= a || length <= 0_i)
            return Shape{a, a, 0_i, -1_i, 0_i, -1_i, length, 0_i};

        auto p = length;
        // |U \ V| = |V \ U| = min(p, b - a): the shift between the two ranges,
        // capped by the window width.
        auto count = min(p, b - a);
        auto u_lo = a - p + 1_i, u_hi = min(a, b - p);
        auto v_lo = max(a, b - p) + 1_i, v_hi = b;

        auto [start_lb, start_ub] = start_bounds;
        // How many of each kind the bounds decide our way. clamp to [0, count]:
        // the bounds may reach past the end of the range in either direction.
        auto kept_u = min(max(0_i, start_lb - u_lo + 1_i), count);
        auto lost_v = min(max(0_i, start_ub - v_lo + 1_i), count);

        return Shape{a, b, u_lo, u_hi, v_lo, v_hi, p, kept_u - lost_v};
    }
}

namespace
{
    // Step 1 of both derivations, and the whole of what they share: three pol
    // lines per time point, ending in
    //     active_t  \/  [s >= t + 1]  \/  ~[s >= t - p + 1] .
    // The first two bridge a flag to an order literal of s, in the same way
    // product_justify's order bridges do: the flag's [f] half and the order
    // literal's defining row share the s bits, which cancel exactly, leaving a
    // two-literal clause after saturation. The third adds active's [f] half,
    // the AND-gate clause active \/ ~before \/ ~after, whose before and after
    // terms then cancel against the two bridges.
    auto emit_per_time_bridges(ProofLogger & logger, const ConstantLengthTask & task, const Shape & shape, ProofLevel level) -> vector<ProofLine>
    {
        auto & tracker = logger.names_and_ids_tracker();
        IntegerVariableID start = task.start;

        vector<ProofLine> per_time;
        per_time.reserve(static_cast<size_t>((shape.b - shape.a).raw_value));
        for (Integer t = shape.a; t < shape.b; ++t) {
            auto idx = static_cast<size_t>((t - task.flags_t_lo).raw_value);

            PolBuilder before_bridge;
            before_bridge.add(ProofLineLabel{tracker.name_of(task.before[idx]) + "[f]"});
            before_bridge.add_for_literal(tracker, start < t + 1_i);
            before_bridge.saturate();
            auto before_clause = before_bridge.emit(logger, level);

            PolBuilder after_bridge;
            after_bridge.add(ProofLineLabel{tracker.name_of(task.after[idx]) + "[f]"});
            after_bridge.add_for_literal(tracker, start >= t - shape.p + 1_i);
            after_bridge.saturate();
            auto after_clause = after_bridge.emit(logger, level);

            PolBuilder step;
            step.add(ProofLineLabel{tracker.name_of(task.active[idx]) + "[f]"});
            step.add(before_clause);
            step.add(after_clause);
            per_time.push_back(step.emit(logger, level));
        }
        return per_time;
    }

    // `[s >= weaker] \/ ~[s >= stronger]`, for weaker <= stronger: a fact about
    // the order encoding rather than about the search state, which is what lets
    // the guarded form be kept. Both defining rows carry the start's bits with
    // opposite signs, so they cancel and saturation leaves the two-literal
    // clause --- the same shape as the flag bridges above.
    auto order_implication(
        ProofLogger & logger, NamesAndIDsTracker & tracker, IntegerVariableID start, Integer weaker, Integer stronger, ProofLevel level) -> ProofLine
    {
        PolBuilder pol;
        pol.add_for_literal(tracker, start >= stronger);
        pol.add_for_literal(tracker, start < weaker);
        pol.saturate();
        return pol.emit(logger, level);
    }
}

auto gcs::innards::window_energy::window_energy_bound(
    Integer length, Integer flags_t_lo, size_t flags_size, Integer lo, Integer hi, pair<Integer, Integer> start_bounds) -> Integer
{
    return shape_of(length, flags_t_lo, flags_size, lo, hi, start_bounds).bound;
}

auto gcs::innards::window_energy::derive_window_energy(ProofLogger & logger, const ReasonLiterals & reason, const ConstantLengthTask & task,
    Integer lo, Integer hi, pair<Integer, Integer> start_bounds, ProofLevel level) -> optional<WindowEnergy>
{
    auto shape = shape_of(task.length, task.flags_t_lo, task.active.size(), lo, hi, start_bounds);
    if (shape.empty() || shape.bound <= 0_i)
        return nullopt;

    auto & tracker = logger.names_and_ids_tracker();
    IntegerVariableID start = task.start;

    auto per_time = emit_per_time_bridges(logger, task, shape, level);

    // Step 2, one pol summing them, into which the order literals telescope.
    PolBuilder sum;
    for (const auto & line : per_time)
        sum.add(line);

    // The "ends by t" survivors. [s >= u] holds under the reason when
    // u <= lb(s), and a unit RUP of it cancels the ~[s >= u] term for free;
    // otherwise the literal axiom [s >= u] >= 0 cancels it at the cost of one.
    auto kept_u = 0_i;
    for (Integer u = shape.u_lo; u <= shape.u_hi; ++u) {
        if (u <= start_bounds.first) {
            sum.add(logger.emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (start >= u) >= 1_i, level));
            ++kept_u;
        }
        else
            sum.add(tracker.xliteral_for_ensuring(task.start >= u), tracker);
    }

    // The "starts after t" survivors, mirror image: ~[s >= v] holds under the
    // reason when v > ub(s).
    auto lost_v = 0_i;
    for (Integer v = shape.v_lo; v <= shape.v_hi; ++v) {
        if (v > start_bounds.second)
            sum.add(logger.emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (start < v) >= 1_i, level));
        else {
            sum.add(! tracker.xliteral_for_ensuring(task.start >= v), tracker);
            ++lost_v;
        }
    }

    // The bound the emission just built must be the one shape_of predicted:
    // the caller scales this line by a height and expects a specific total, so
    // a disagreement here would surface only as a rejected proof much later.
    if (kept_u - lost_v != shape.bound)
        throw ProofError{"window energy derivation and its predicted bound disagree"};

    return WindowEnergy{sum.emit(logger, level), shape.bound, shape.a, shape.b};
}

auto gcs::innards::window_energy::derive_guarded_window_energy(ProofLogger & logger, const ConstantLengthTask & task, Integer lo, Integer hi,
    Integer high_guard, ProofLevel level) -> optional<GuardedWindowEnergy>
{
    // The guards stand in for the bounds a firing would have had: every "ends
    // by t" survivor is kept, and a "starts after t" survivor is lost exactly
    // when it sits below the threshold. So the shape, and the bound it
    // predicts, are the reason-backed ones for those bounds.
    //
    // The low one is the *clipped* window start, not the requested one. Where a
    // task's flags begin after the window does, the two differ, and passing the
    // requested start would have the shape believe the low guard leaves some of
    // the "ends by t" survivors undecided --- costing bound the derivation does
    // not actually lose.
    auto window_lo = max(lo, task.flags_t_lo);
    auto shape = shape_of(task.length, task.flags_t_lo, task.active.size(), lo, hi, pair{window_lo, high_guard - 1_i});
    if (shape.empty() || shape.bound <= 0_i)
        return nullopt;

    auto & tracker = logger.names_and_ids_tracker();
    IntegerVariableID start = task.start;

    // The strongest of the "ends by t" survivors, and so the one the others
    // weaken onto. It is the clipped window's start whenever the task can be
    // contained at all, which is the only case a citer has.
    auto low_guard = shape.u_hi;

    auto per_time = emit_per_time_bridges(logger, task, shape, level);

    PolBuilder sum;
    for (const auto & line : per_time)
        sum.add(line);

    // Each ~[s >= u] is cancelled by the order encoding's own monotonicity
    // rather than by a bound: `[s >= u] \/ ~[s >= low_guard]` turns it into
    // ~[s >= low_guard], so the survivors collapse onto one literal carrying
    // their whole count.
    auto low_coeff = 0_i;
    for (Integer u = shape.u_lo; u <= shape.u_hi; ++u) {
        // The strongest survivor is already the guard, and adding anything for
        // it would discharge it at the cost of a unit of the bound instead.
        if (u != low_guard)
            sum.add(order_implication(logger, tracker, start, u, low_guard, level));
        ++low_coeff;
    }

    // Mirror image, except that a survivor below the threshold cannot be
    // weakened onto it --- the implication runs the wrong way --- so it is
    // discharged by its own literal axiom, at the cost of one unit of the
    // bound. That is where the clipping comes from: the bound falls by exactly
    // the number of time points the threshold puts out of reach.
    auto bound = 0_i;
    for (Integer v = shape.v_lo; v <= shape.v_hi; ++v) {
        if (v < high_guard)
            sum.add(! tracker.xliteral_for_ensuring(task.start >= v), tracker);
        else {
            if (v != high_guard)
                sum.add(order_implication(logger, tracker, start, high_guard, v, level));
            ++bound;
        }
    }

    // The `v == high_guard` and `u == low_guard` survivors need no implication
    // of their own, so the guards' coefficients are what the counting says
    // rather than what was emitted. As in the reason-backed form, a
    // disagreement here would surface only as a rejected proof much later.
    if (bound != shape.bound)
        throw ProofError{"guarded window energy derivation and its predicted bound disagree"};

    return GuardedWindowEnergy{sum.emit(logger, level), bound, shape.a, shape.b, low_guard, low_coeff, high_guard};
}
