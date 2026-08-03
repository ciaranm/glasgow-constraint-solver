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

    // Step 1, three pol lines per time point, ending in
    //     active_t  \/  [s >= t + 1]  \/  ~[s >= t - p + 1] .
    // The first two bridge a flag to an order literal of s, in the same way
    // product_justify's order bridges do: the flag's [f] half and the order
    // literal's defining row share the s bits, which cancel exactly, leaving a
    // two-literal clause after saturation. The third adds active's [f] half,
    // the AND-gate clause active \/ ~before \/ ~after, whose before and after
    // terms then cancel against the two bridges.
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
