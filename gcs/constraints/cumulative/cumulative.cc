#include <gcs/constraints/cumulative/cumulative.hh>
#include <gcs/constraints/cumulative/hints.hh>
#include <gcs/constraints/cumulative/propagate.hh>
#include <gcs/constraints/innards/window_energy.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/power.hh>
#include <gcs/innards/proofs/bits_encoding.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/subset_sum_strengthening.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <algorithm>
#include <cstdint>
#include <memory>
#include <optional>
#include <sstream>
#include <string>
#include <utility>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

using namespace gcs;
using namespace gcs::innards;

using std::make_optional;
using std::make_shared;
using std::make_unique;
using std::max;
using std::min;
using std::move;
using std::optional;
using std::pair;
using std::size_t;
using std::string;
using std::stringstream;
using std::uint64_t;
using std::unique_ptr;
using std::vector;
using std::ranges::fill;
using std::ranges::find;
using std::ranges::none_of;
using std::ranges::sort;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

namespace
{
    // The variable-height contribution h_i·active is linearised over cake's
    // per-bit contribution flags cc_k (weight 2^k): contrib = Σ 2^k · cc_k.
    auto contrib_sum_of(const vector<ProofFlag> & cc) -> WPBSum
    {
        WPBSum sum;
        for (Integer k = 0_i; k.raw_value < static_cast<long long>(cc.size()); ++k)
            sum += power2(k) * cc[k.raw_value];
        return sum;
    }
}

Cumulative::Cumulative(vector<IntegerVariableID> starts, vector<IntegerVariableID> lengths, vector<IntegerVariableID> heights,
    IntegerVariableID capacity) : _starts(move(starts)), _lengths(move(lengths)), _heights(move(heights)), _capacity(capacity), _capacity_val(0_i)
{
    if (_starts.size() != _lengths.size() || _starts.size() != _heights.size())
        throw InvalidProblemDefinitionException{"Cumulative: starts, lengths, heights must have the same size"};
    // Constant non-negativity is checked here; variable lengths/heights/
    // capacity are checked in prepare(), where their domains first become
    // available.
    if (is_constant_variable(_capacity) && constant_value_of(_capacity) < 0_i)
        throw InvalidProblemDefinitionException{"Cumulative: capacity must be non-negative"};
    for (const auto & l : _lengths)
        if (is_constant_variable(l) && constant_value_of(l) < 0_i)
            throw InvalidProblemDefinitionException{"Cumulative: lengths must be non-negative"};
    for (const auto & h : _heights)
        if (is_constant_variable(h) && constant_value_of(h) < 0_i)
            throw InvalidProblemDefinitionException{"Cumulative: heights must be non-negative"};
}

Cumulative::Cumulative(vector<IntegerVariableID> starts, vector<Integer> lengths, vector<Integer> heights, Integer capacity) :
    Cumulative(move(starts), as_constant_variables(lengths), as_constant_variables(heights), constant_variable(capacity))
{
}

Cumulative::Cumulative(vector<IntegerVariableID> starts, vector<IntegerVariableID> lengths, vector<IntegerVariableID> heights,
    vector<IntegerVariableID> presences, IntegerVariableID capacity) : Cumulative(move(starts), move(lengths), move(heights), capacity)
{
    _presences = move(presences);
    if (_starts.size() != _presences.size())
        throw InvalidProblemDefinitionException{"Cumulative: starts and presences must have the same size"};
    // A constant presence is checked here; a variable one is checked in
    // prepare(), where its domain first becomes available.
    for (const auto & p : _presences)
        if (is_constant_variable(p) && constant_value_of(p) != 0_i && constant_value_of(p) != 1_i)
            throw InvalidProblemDefinitionException{"Cumulative: presences must be within {0, 1}"};
}

auto Cumulative::with_rules(CumulativeRules rules) -> Cumulative &
{
    _rules = rules;
    return *this;
}

auto Cumulative::with_proof_mutation(CumulativeProofMutation mutation) -> Cumulative &
{
    _proof_mutation = mutation;
    return *this;
}

auto Cumulative::with_presence_mutation(CumulativePresenceMutation mutation) -> Cumulative &
{
    _presence_mutation = mutation;
    return *this;
}

auto Cumulative::clone() const -> unique_ptr<Constraint>
{
    auto result = _presences.empty() ? make_unique<Cumulative>(_starts, _lengths, _heights, _capacity)
                                     : make_unique<Cumulative>(_starts, _lengths, _heights, _presences, _capacity);
    result->with_rules(_rules);
    result->with_proof_mutation(_proof_mutation);
    result->with_presence_mutation(_presence_mutation);
    return result;
}

auto Cumulative::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    auto n = _starts.size();

    // Non-negativity for variable durations/demands/capacity (constants are
    // checked in the constructor): a negative length/height/capacity has no
    // sensible cumulative interpretation, so reject it now that the domains are
    // available rather than producing nonsense.
    for (const auto & l : _lengths)
        if (! is_constant_variable(l) && initial_state.lower_bound(l) < 0_i)
            throw InvalidProblemDefinitionException{"Cumulative: lengths must be non-negative"};
    for (const auto & h : _heights)
        if (! is_constant_variable(h) && initial_state.lower_bound(h) < 0_i)
            throw InvalidProblemDefinitionException{"Cumulative: heights must be non-negative"};
    if (! is_constant_variable(_capacity) && initial_state.lower_bound(_capacity) < 0_i)
        throw InvalidProblemDefinitionException{"Cumulative: capacity must be non-negative"};

    // Resolve each task's presence to the variable that has to appear in its
    // active flag, or nullopt when the task is unconditionally present ---
    // by the same rule anything pinning these flags has to apply, which is why
    // task_presence is shared rather than open-coded here.
    _presence.assign(n, std::nullopt);
    vector<bool> never_present(n, false);
    for (size_t i = 0; i < n; ++i) {
        auto resolved = task_presence(_presences.empty() ? std::nullopt : make_optional(_presences[i]), "Cumulative");
        _presence[i] = resolved.literal;
        never_present[i] = resolved.never_present;

        // Only now are the domains available, which is why a variable
        // presence is range-checked here rather than in the constructor.
        if (resolved.literal && ! is_constant_variable(*resolved.literal)) {
            auto [lo, hi] = initial_state.bounds(*resolved.literal);
            if (lo < 0_i || hi > 1_i)
                throw InvalidProblemDefinitionException{"Cumulative: presences must be within {0, 1}"};
        }
    }

    // Resolve snapshots used by define_proof_model and the propagator. For a
    // variable length/height, _*_vals[i] is a placeholder 0 (the propagator
    // reads the bound from the state and the proof uses the variable /
    // _contrib_flags instead); _*_ub[i] is the initial upper bound, used to size
    // the possible-active window / contrib domain and to filter tasks that can
    // never raise the profile.
    _length_vals.clear();
    _length_lb.clear();
    _length_ub.clear();
    _height_vals.clear();
    _height_ub.clear();
    _length_vals.reserve(n);
    _length_lb.reserve(n);
    _length_ub.reserve(n);
    _height_vals.reserve(n);
    _height_ub.reserve(n);
    for (const auto & l : _lengths) {
        _length_vals.push_back(is_constant_variable(l) ? constant_value_of(l) : 0_i);
        _length_lb.push_back(initial_state.lower_bound(l));
        _length_ub.push_back(initial_state.upper_bound(l));
    }
    for (const auto & h : _heights) {
        _height_vals.push_back(is_constant_variable(h) ? constant_value_of(h) : 0_i);
        _height_ub.push_back(initial_state.upper_bound(h));
    }
    if (is_constant_variable(_capacity))
        _capacity_val = constant_value_of(_capacity);

    // Tasks whose length can only ever be 0, or whose height can only ever be 0,
    // or which are constantly absent, never raise the load profile.
    _active_tasks.reserve(n);
    for (size_t i = 0; i < n; ++i)
        if (_length_ub[i] > 0_i && _height_ub[i] > 0_i && ! never_present[i])
            _active_tasks.push_back(i);

    if (_active_tasks.empty())
        return false;

    // The per-(i,t) flags span the possible-active window, so this is the
    // windowing everything downstream --- a derived constraint, a presolver ---
    // has to agree with, and is why it is not written out here.
    _per_task_t_lo.assign(n, 0_i);
    _per_task_t_hi.assign(n, 0_i);
    for (auto i : _active_tasks) {
        auto window = cumulative_task_window(initial_state, _starts[i], _lengths[i]);
        _per_task_t_lo[i] = window.lo;
        _per_task_t_hi[i] = window.hi;
    }

    if (_rules.overload) {
        auto overload_data =
            prepare_cumulative_overload_check(_starts, _lengths, _heights, _active_tasks, _per_task_t_lo, _per_task_t_hi, initial_state);
        _overload_tasks = move(overload_data.overload_tasks);
        _time_slot_prefix = move(overload_data.time_slot_prefix);
        _time_slot_lo = overload_data.time_slot_lo;
    }

    return true;
}

auto gcs::innards::cumulative_task_window(const State & initial_state, const IntegerVariableID & start, const IntegerVariableID & length)
    -> CumulativeTaskWindow
{
    auto [s_lo, s_hi] = initial_state.bounds(start);
    return CumulativeTaskWindow{s_lo, s_hi + initial_state.upper_bound(length) - 1_i};
}

auto gcs::innards::prepare_cumulative_overload_check(const vector<IntegerVariableID> & starts, const vector<IntegerVariableID> & lengths,
    const vector<IntegerVariableID> & heights, const vector<size_t> & active_tasks, const vector<Integer> & per_task_t_lo,
    const vector<Integer> & per_task_t_hi, const State & initial_state) -> CumulativeOverloadData
{
    CumulativeOverloadData result;
    // Which tasks the window-energy lemma can speak about: a constant height
    // (so the task's load in C_t is h·active rather than the bit-linearised
    // contrib), and a start that is a plain variable with an order encoding,
    // since the lemma bridges the before/after flags to the start's order
    // literals. A task that is not eligible is not lost to the check: whatever
    // it must occupy still counts, through the profile term of the (TTOC)
    // strengthening.
    //
    // The height half is looser than it reads. A *derived* Cumulative's tasks
    // carry constant heights by construction, so one whose donor height was a
    // variable arrives here already converted to the demand it guarantees and
    // passes --- which is how an all-variable-height donor's energy gets
    // counted at all. A posted constraint's variable height is still turned
    // away, and need not be: the same conversion would serve, and #689's
    // remaining half is what it would take.
    //
    // A *variable* length is admitted (#689), at the length it is guaranteed to
    // reach rather than at the one it might: the lemma counts the task over
    // [start, start + lb(length)), which its execution interval contains, by
    // bridging its `after` flags back onto the start's order literals through
    // the length's own. What that needs from here is a length whose order
    // literals exist to be bridged with, so a plain variable, and one that can
    // be positive at all --- a task whose length can only be zero is not an
    // active task in the first place. Whether the bound it reaches is worth
    // anything is asked at every node, in the candidate sweep, and not here.
    //
    // Presence is not among the tests, and deliberately so. What is asked here
    // is whether the lemma could *ever* speak about a task, which is a question
    // about how it was posted and is settled once; whether it may speak about
    // it now is a question about the search, and is asked at every node, where
    // the propagator skips a task not yet known present and carries the
    // presence literals of the ones it did use into the reason. A task that can
    // never be present at all is gone before this is called, `active_tasks`
    // having dropped it.
    // A variable whose domain is exactly {0, 1} is direct-only encoded, so it
    // has no order literals for the lemma's bridges to cancel against. Asked of
    // a variable length as well as of the start: both are bridged through.
    auto direct_only_encoded = [&](const IntegerVariableID & v) {
        auto [lo, hi] = initial_state.bounds(v);
        return lo == 0_i && hi == 1_i;
    };

    result.overload_tasks.clear();
    for (auto i : active_tasks) {
        if (! is_constant_variable(heights[i]) || constant_value_of(heights[i]) <= 0_i)
            continue;
        if (! std::holds_alternative<SimpleIntegerVariableID>(starts[i]) || direct_only_encoded(starts[i]))
            continue;
        if (is_constant_variable(lengths[i])) {
            if (constant_value_of(lengths[i]) <= 0_i)
                continue;
        }
        else if (! std::holds_alternative<SimpleIntegerVariableID>(lengths[i]) || initial_state.upper_bound(lengths[i]) <= 0_i ||
            direct_only_encoded(lengths[i]))
            continue;
        result.overload_tasks.push_back(i);
    }

    if (result.overload_tasks.empty())
        return result;

    // Count the time points at which some task can be active, which is exactly
    // where define_proof_model writes a capacity line. A difference array over
    // the per-task windows, prefix-summed, so a window's count is one
    // subtraction.
    Integer global_lo = per_task_t_lo[active_tasks.front()], global_hi = per_task_t_hi[active_tasks.front()];
    for (auto i : active_tasks) {
        global_lo = min(global_lo, per_task_t_lo[i]);
        global_hi = max(global_hi, per_task_t_hi[i]);
    }

    auto range = (global_hi - global_lo + 1_i).raw_value;
    vector<long long> starting_or_ending(static_cast<size_t>(range) + 1, 0);
    for (auto i : active_tasks) {
        ++starting_or_ending[static_cast<size_t>((per_task_t_lo[i] - global_lo).raw_value)];
        --starting_or_ending[static_cast<size_t>((per_task_t_hi[i] + 1_i - global_lo).raw_value)];
    }

    result.time_slot_lo = global_lo;
    result.time_slot_prefix.assign(static_cast<size_t>(range) + 1, 0_i);
    long long covering = 0;
    for (size_t k = 0; k < static_cast<size_t>(range); ++k) {
        covering += starting_or_ending[k];
        result.time_slot_prefix[k + 1] = result.time_slot_prefix[k] + (covering > 0 ? 1_i : 0_i);
    }

    return result;
}

auto Cumulative::define_proof_model(ProofModel & model, const State &) -> void
{
    // A propagator that infers what it cannot justify is worse than one that
    // declines: refuse here rather than emit a proof VeriPB will reject.
    if (_rules.energetic_edge_finding)
        throw UnimplementedException{"energetic edge-finding is not yet certified"};

    // Time-table OPB encoding:
    //   for each task i and each time point t in its possible-active range:
    //     before_{i,t}  ⇔  starts[i] ≤ t
    //     after_{i,t}   ⇔  starts[i] ≥ t − lengths[i] + 1
    //     active_{i,t} ⇔  before_{i,t} ∧ after_{i,t} [ ∧ presences[i] = 1 ]
    //   for each time point t:
    //     Σ heights[i] · active_{i,t} ≤ capacity
    _before_flags.assign(_starts.size(), {});
    _after_flags.assign(_starts.size(), {});
    _active_flags.assign(_starts.size(), {});
    _contrib_flags.assign(_starts.size(), {});
    _end.assign(_starts.size(), std::nullopt);

    Integer global_lo = 0_i, global_hi = -1_i;
    bool first = true;
    for (auto i : _active_tasks) {
        auto t_lo = _per_task_t_lo[i], t_hi = _per_task_t_hi[i];
        if (first || t_lo < global_lo)
            global_lo = t_lo;
        if (first || t_hi > global_hi)
            global_hi = t_hi;
        first = false;

        // When both start and length vary, after_{i,t} ⇔ s_i + l_i ≥ t+1 is a
        // two-variable fact whose pinning RUP cannot reach from the operands'
        // bounds. We still reify after on s_i + l_i directly (matching cake), but
        // give the propagator a single-variable handle by introducing a proof-only
        // end = s_i + l_i. Crucially end has NO OPB encoding (cake has no such
        // variable): it is bit-defined inside the proof by the install_initialiser
        // (introduce_bits_of), which also emits the `end ≥ t+1 → after` bridge
        // lemma per (i,t). nullopt unless both operands vary. The range must
        // cover s + l in full or introduce_bits_of's redundancy goals are
        // unprovable: lb(s) + lb(l) can be negative (a start before time 0,
        // issue #553), in which case end gets a sign bit; keep 0 as the lower
        // bound otherwise --- end ≥ 0 is the one unsigned boundary pin that
        // would be a tautology, and verified instances' tracked bounds stay
        // untouched.
        if (! is_constant_variable(_starts[i]) && ! is_constant_variable(_lengths[i]))
            _end[i] =
                model.create_proof_only_integer_variable_in_proof(min(0_i, _per_task_t_lo[i] + _length_lb[i]), _per_task_t_hi[i] + 1_i, "cumend");

        for (Integer t = t_lo; t <= t_hi; ++t) {
            // Name the flags to match cake_pb_cp's verified cumulative encoder
            // (its value-indexed v[id][i_t][cb] / [ca] / [cact], keyed by task i
            // and integer time t), so the proof's references to them resolve
            // against cake's re-derived OPB in the verified-encoding chain (the
            // solver's per-task window is a subset of cake's global one, so every
            // flag we cite is one cake also defines). cake's structurally-matching
            // definitions (before ⇔ s≤t, after ⇔ s+l≥t+1, active ⇔ before∧after)
            // make this a naming conform with no propagator change.
            std::vector<long long> it{static_cast<long long>(i), t.raw_value};
            auto before = model.create_proof_flag_values_fully_reifying(_constraint_id, it, "cb", WPBSum{} + 1_i * _starts[i] <= t);
            // after_{i,t} ⇔ task i not yet finished at t ⇔ s_i + l_i ≥ t + 1.
            // Constant length: single-variable s_i ≥ t−l+1. Variable length:
            // reify on s_i + l_i directly (any constant operand folds in), which
            // matches cake_pb_cp's after ⇔ s + l ≥ t+1. The proof-only end (when
            // both vary) is NOT used in this reification; it is only the
            // single-variable handle the propagator pins through, bridged to this
            // flag by the lemma the initialiser emits.
            auto after = is_constant_variable(_lengths[i])
                ? model.create_proof_flag_values_fully_reifying(_constraint_id, it, "ca", WPBSum{} + 1_i * _starts[i] >= t - _length_vals[i] + 1_i)
                : model.create_proof_flag_values_fully_reifying(_constraint_id, it, "ca", WPBSum{} + 1_i * _starts[i] + 1_i * _lengths[i] >= t + 1_i);
            // active_{i,t} ⇔ before ∧ after, plus the presence conjunct for an
            // optional task. The presence literal is the {0,1} variable's single
            // PB atom, so the three-way AND costs one more term in the same two
            // reification halves --- no extra flag, and nothing else in the
            // encoding has to know whether the task is optional. An absent task
            // fails the AND at every t, so it drops out of every capacity row,
            // which is exactly "an absent task consumes nothing".
            auto active_conjuncts = WPBSum{} + 1_i * before + 1_i * after;
            auto active_arity = 2_i;
            if (_presence[i]) {
                active_conjuncts += 1_i * (*_presence[i] == 1_i);
                active_arity = 3_i;
            }
            auto active = model.create_proof_flag_values_fully_reifying(_constraint_id, it, "cact", move(active_conjuncts) >= active_arity);
            _before_flags[i].push_back(before);
            _after_flags[i].push_back(after);
            _active_flags[i].push_back(active);

            // For a variable height, the task's load contribution at t is the
            // product height·active, which is nonlinear. Linearise it over cake's
            // per-bit contribution flags cc_k (weight 2^k), so contrib = Σ 2^k·cc_k
            // (same encoding cake_pb_cp emits, so the load reasoning chain-verifies):
            //   active   ⇒ contrib = h   (contrib − h ≥ 0 and ≤ 0)
            //   ¬active  ⇒ contrib = 0   (contrib ≤ 0; cc_k ≥ 0 inherently)
            // The bit count matches the proof-only bits encoding of [0, ub(h)], and
            // the flags carry no domain bound of their own (cle/cz constrain them,
            // exactly as cake does).
            if (! is_constant_variable(_heights[i])) {
                auto highest_bit_shift = std::get<0>(get_bits_encoding_coeffs(0_i, _height_ub[i]));
                std::vector<ProofFlag> cc;
                for (Integer k = 0_i; k <= highest_bit_shift; ++k)
                    cc.push_back(model.names_and_ids_tracker().create_proof_flag_values(
                        _constraint_id, std::vector<long long>{static_cast<long long>(i), t.raw_value, k.raw_value}, "cc"));
                // Labelled, with cake's own names for them: it emits all three
                // under @c[id][i_t_cge] / [_cle] / [_cz], with the coefficients
                // we do, so these are the labels a citer of ours resolves
                // against cake's OPB as well as our own. The `cge` half is what
                // converts a variable height into a constant one for a derived
                // constraint (recover_constant_argument_row); the other two are
                // labelled to keep the family whole rather than because
                // anything cites them yet.
                auto contrib = contrib_sum_of(cc);
                model.add_labelled_constraint(_constraint_id, ConstraintProofModelData<Cumulative>::contribution_ge_row_role(i, t),
                    contrib + -1_i * _heights[i] >= 0_i, HalfReifyOnConjunctionOf{active});
                model.add_labelled_constraint(_constraint_id, ConstraintProofModelData<Cumulative>::contribution_le_row_role(i, t),
                    contrib + -1_i * _heights[i] <= 0_i, HalfReifyOnConjunctionOf{active});
                model.add_labelled_constraint(_constraint_id, ConstraintProofModelData<Cumulative>::contribution_zero_row_role(i, t), contrib <= 0_i,
                    HalfReifyOnConjunctionOf{! active});
                _contrib_flags[i].push_back(move(cc));
            }
        }
    }

    for (Integer t = global_lo; t <= global_hi; ++t) {
        WPBSum load;
        bool any = false;
        for (auto i : _active_tasks) {
            if (t < _per_task_t_lo[i] || t > _per_task_t_hi[i])
                continue;
            auto idx = (t - _per_task_t_lo[i]).raw_value;
            if (is_constant_variable(_heights[i]))
                load += _height_vals[i] * _active_flags[i][idx];
            else
                for (Integer k = 0_i; k.raw_value < static_cast<long long>(_contrib_flags[i][idx].size()); ++k)
                    load += power2(k) * _contrib_flags[i][idx][k.raw_value];
            any = true;
        }
        if (any) {
            // Σ heights[i]·active[i,t] ≤ capacity. When the capacity is a
            // variable, move it to the left as a (−1)·capacity term so the
            // constraint stays a single linear inequality with RHS 0.
            //
            // cake_pb_cp labels its per-time load constraint @c[id][cap_<t>], and
            // its per-task time windowing matches ours, so our load line for time t
            // is cake's cap line for time t. Emit the same label so the verified
            // chain references it by name rather than position.
            auto role = "cap_" + std::to_string(t.raw_value);
            auto line = is_constant_variable(_capacity) ? model.add_labelled_constraint(_constraint_id, role, load <= _capacity_val)
                                                        : model.add_labelled_constraint(_constraint_id, role, move(load) + -1_i * _capacity <= 0_i);
            _capacity_lines.emplace(t, line);
        }
    }
}

auto Cumulative::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    for (auto i : _active_tasks)
        triggers.on_bounds.emplace_back(_starts[i]);
    // A tightening of the capacity's upper bound can newly overflow the load
    // profile, so re-fire on it too (constant capacity never changes).
    if (! is_constant_variable(_capacity))
        triggers.on_bounds.emplace_back(_capacity);
    // A rise in a task's guaranteed height (lb) raises the mandatory load, so
    // re-fire on variable-height bound changes too.
    for (auto i : _active_tasks)
        if (! is_constant_variable(_heights[i]))
            triggers.on_bounds.emplace_back(_heights[i]);
    // A rise in a task's guaranteed length (lb) extends its mandatory part, so
    // re-fire on variable-length bound changes too.
    for (auto i : _active_tasks)
        if (! is_constant_variable(_lengths[i]))
            triggers.on_bounds.emplace_back(_lengths[i]);
    // A task joins the load profile the moment its presence is fixed to 1, and
    // leaves the falsification search the moment it is fixed to 0, so an
    // optional task's presence has to wake the propagator as much as its start
    // does. A {0,1} variable's only possible change is being fixed, so
    // on_bounds and on_instantiated coincide here.
    for (auto i : _active_tasks)
        if (_presence[i] && ! is_constant_variable(*_presence[i]))
            triggers.on_instantiated.emplace_back(*_presence[i]);

    // Per variable-duration task, the in-proof `end ≥ s + l` line, filled by the
    // initialiser and read by the propagator's materialise_after_sum. Shared so
    // the cache survives across propagator calls --- and so that the
    // propagator, whose inputs are built here and now, gets a line the
    // initialiser has not derived yet.
    auto end_ge_lines = make_shared<vector<std::optional<ProofLine>>>(_starts.size());

    propagators.install_initialiser([id = constraint_id(), starts = _starts, lengths = _lengths, ends = _end, active_tasks = _active_tasks,
                                        after_flags = _after_flags, end_ge_lines](State &, auto &, ProofLogger * const logger) -> void {
        if (! logger || logger->get_assertion_level() > AssertionLevel::Off)
            return;
        auto & tracker = logger->names_and_ids_tracker();
        // Bit-define each variable-duration end = s + l as a conservative
        // extension FIRST (introduce_bits_of needs end's bits fresh for its
        // witnesses), caching end's {end_ge, end_le}. cake has no end variable,
        // so this lives entirely in the proof --- nothing in the OPB to match.
        //
        // end_ge is published, because a derived Cumulative over this task pins
        // its `after` flags the same way and through the same line; end_le is
        // the bridge lemma's business alone, and stays here.
        vector<std::optional<ProofLine>> end_le(starts.size());
        for (auto i : active_tasks)
            if (ends[i].has_value()) {
                auto lines = logger->introduce_bits_of(WPBSum{} + 1_i * starts[i] + 1_i * lengths[i], *ends[i], ProofLevel::Top);
                (*end_ge_lines)[i] = lines.first;
                end_le[i] = lines.second;
                tracker.publish_derived_line(id, ConstraintProofModelData<Cumulative>::end_lower_bound_role(i), lines.first);
            }
        // Then, per (i, t), emit the bridge lemma `end ≥ t+1 → after`:
        //   pol( @v[id][i_t][ca][f] : ¬after → s+l ≤ t )  +  ( end ≤ s+l )
        //   = ( M·after − end + t ≥ 0 ).
        // The s+l bits cancel exactly, leaving a single-variable-in-end handle
        // that makes the propagator's after pin RUP-closable even though after
        // is reified on the two-variable s+l. end_le is the cancelling term.
        //
        // These need no publishing at all: they go out at ProofLevel::Top over
        // exactly the (i, t) pairs this constraint gave the task a window for,
        // so unit propagation finds them for whoever pins one of those flags,
        // and a citer that could ask about a wider window would already have
        // been turned away by the flag lookup.
        for (auto i : active_tasks) {
            if (! ends[i].has_value())
                continue;
            for (const auto & after : after_flags[i]) {
                PolBuilder lemma;
                // `name_of` and not `pb_file_string_for`, which is the other
                // base a flag's reification halves can be labelled under: these
                // flags come from create_proof_flag_values_fully_reifying, and
                // that is the overload whose `[r]` / `[f]` labels are built off
                // `name_of`. `pb_file_string_for` is the base
                // add_two_way_reified_constraint uses, for flags with no
                // ConstraintID to key them. Getting it the wrong way round is
                // loud --- there is no such label --- but it is worth not
                // having to find that out.
                lemma.add(ProofLineLabel{tracker.name_of(after) + "[f]"});
                lemma.add(*end_le[i]);
                lemma.emit(*logger, ProofLevel::Top);
            }
        }
    });

    CumulativeInputs inputs{.owner = constraint_id(),
        .starts = move(_starts),
        .lengths = move(_lengths),
        .heights = move(_heights),
        .capacity = _capacity,
        .presence = move(_presence),
        .active_tasks = move(_active_tasks),
        .before_flags = move(_before_flags),
        .after_flags = move(_after_flags),
        .active_flags = move(_active_flags),
        .contrib_flags = move(_contrib_flags),
        .per_task_t_lo = move(_per_task_t_lo),
        .per_task_t_hi = move(_per_task_t_hi),
        .end_ge_lines = end_ge_lines,
        .capacity_lines = move(_capacity_lines),
        .rules = _rules,
        .proof_mutation = _proof_mutation,
        .presence_mutation = _presence_mutation,
        .overload_tasks = move(_overload_tasks),
        .time_slot_prefix = move(_time_slot_prefix),
        .time_slot_lo = _time_slot_lo,
        .guarded_energy =
            std::make_shared<std::map<std::tuple<size_t, Integer, Integer, Integer, Integer, Integer>, window_energy::GuardedWindowEnergy>>()};

    propagators.install(
        constraint_id(),
        [inputs = move(inputs)](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            return propagate_cumulative(inputs, state, inference, logger);
        },
        triggers);
}

auto gcs::innards::propagate_cumulative(const CumulativeInputs & inputs, const State & state, auto & inference, ProofLogger * const logger)
    -> PropagatorState
{
    // Named the way the propagator body has always named them, so that what
    // follows is the same code whether a posted Cumulative or a derived one
    // supplied the flags and lines.
    const auto & starts = inputs.starts;
    const auto & lengths_var = inputs.lengths;
    const auto & heights_var = inputs.heights;
    const auto & capacity_var = inputs.capacity;
    const auto & active_tasks = inputs.active_tasks;
    const auto & before_flags = inputs.before_flags;
    const auto & after_flags = inputs.after_flags;
    const auto & active_flags = inputs.active_flags;
    const auto & contrib_flags = inputs.contrib_flags;
    const auto & per_task_t_lo = inputs.per_task_t_lo;
    const auto & per_task_t_hi = inputs.per_task_t_hi;
    const auto & end_ge_lines = inputs.end_ge_lines;
    const auto & capacity_lines = inputs.capacity_lines;
    const auto & rules = inputs.rules;
    const auto & mutation = inputs.proof_mutation;
    const auto & presence = inputs.presence;
    const auto & presence_mutation = inputs.presence_mutation;
    const auto & overload_tasks = inputs.overload_tasks;
    const auto & time_slot_prefix = inputs.time_slot_prefix;
    const auto & time_slot_lo = inputs.time_slot_lo;
    const auto & owner = inputs.owner;

    // The capacity may be a variable: the load profile is infeasible
    // only when it exceeds the *largest* still-allowed capacity, so the
    // threshold for every overflow/blocked test is ub(capacity). When
    // capacity is a genuine variable its bound is part of every reason.
    auto capacity = state.upper_bound(capacity_var);

    // A height may be a variable: a task's *guaranteed* contribution to
    // the load is its smallest still-allowed height, lb(h_i). For a
    // constant height lb(h_i) is just its value. Variable heights' bounds
    // are part of every reason, and the proof uses the cc flags.
    auto hlb = [&](size_t i) { return state.lower_bound(heights_var[i]); };
    auto h_is_var = [&](size_t i) { return ! is_constant_variable(heights_var[i]); };

    // A length may be a variable: a task's *mandatory* part and its
    // guaranteed footprint when placed use the smallest still-allowed
    // duration lb(l_i); the possible-active window uses ub(l_i). For a
    // constant length both are its value. Variable-length bounds join
    // every reason.
    auto llb = [&](size_t i) { return state.lower_bound(lengths_var[i]); };
    auto lub = [&](size_t i) { return state.upper_bound(lengths_var[i]); };
    auto l_is_var = [&](size_t i) { return ! is_constant_variable(lengths_var[i]); };
    auto s_is_var = [&](size_t i) { return ! is_constant_variable(starts[i]); };

    // The task as the window-energy lemma sees it. Only ever called for a task
    // prepare_cumulative_overload_check kept, so the start --- and a variable
    // length --- really are plain variables. A variable length goes along with
    // lb(l_i) rather than instead of it: the flags it has to bridge through are
    // reified on the two-variable s_i + l_i, and the lemma needs to know that to
    // read them, while what it counts the task at is still the length the task
    // is guaranteed to run for.
    auto lemma_task = [&](size_t i) {
        return window_energy::Task{std::get<SimpleIntegerVariableID>(starts[i]), llb(i), per_task_t_lo[i], before_flags[i], after_flags[i],
            active_flags[i], l_is_var(i) ? make_optional(std::get<SimpleIntegerVariableID>(lengths_var[i])) : optional<SimpleIntegerVariableID>{}};
    };

    // A task with no presence variable is always here. An optional one is here
    // only once its presence is fixed to 1: until then it contributes nothing
    // to the profile and nothing to the overload check's energy, and nothing
    // may be inferred about its start, since a prune that is only valid when
    // the task is present would be plain wrong if it turns out absent. Fixed
    // to 0, it is gone for good and every loop below skips it.
    auto is_present = [&](size_t i) { return ! presence[i] || state.lower_bound(*presence[i]) == 1_i; };
    auto is_absent = [&](size_t i) { return presence[i] && state.upper_bound(*presence[i]) == 0_i; };

    // For a task whose start AND length are both variables, after_{i,t}
    // is reified on s_i + l_i. To pin after = 1 we first materialise the
    // single-variable end ≥ s_lo + lb(l_i) with a pol over end's in-proof
    // `end ≥ s + l` line plus the two operand order-literal defining lines;
    // the after = 1 RUP is then single-variable in end, closing against the
    // `end ≥ t+1 → after` bridge lemma the initialiser emitted (just like
    // the constant-duration case). s_lo is the start lower bound that, with
    // lb(l_i), reaches t+1: the chain running bound for lb-push, t−lb(l_j)+1
    // (= ¬ext_lit) for ub-push, lb(s_i) for a mandatory task. Only needed
    // when both operands vary (else after is already single-variable).
    auto materialise_after_sum = [&](size_t i, Integer s_lo) -> void {
        if (! (l_is_var(i) && s_is_var(i)))
            return;
        PolBuilder sp;
        sp.add(*(*end_ge_lines)[i]);
        sp.add_for_literal(logger->names_and_ids_tracker(), starts[i] >= s_lo);
        sp.add_for_literal(logger->names_and_ids_tracker(), lengths_var[i] >= llb(i));
        sp.emit(*logger, ProofLevel::Temporary);
    };

    vector<IntegerVariableID> reason_vars = starts;
    if (! is_constant_variable(capacity_var))
        reason_vars.push_back(capacity_var);
    for (auto i : active_tasks) {
        if (h_is_var(i))
            reason_vars.push_back(heights_var[i]);
        if (l_is_var(i))
            reason_vars.push_back(lengths_var[i]);
    }

    // Presence enters the reason as an explicit literal per task known present,
    // rather than by putting the variable in reason_vars: an undecided presence
    // has no fact to record (a task not known present is simply not in the
    // profile, and staying out of it is monotone as the domain shrinks), and
    // generic_reason would contribute the pair of trivial bounds 0 ≤ p ≤ 1 for
    // it, which says nothing and costs an order atom on a variable whose whole
    // encoding is one PB literal. Every inference below reasons only about
    // tasks known present, so this one list serves all of them --- including
    // the overload check, whose energy set is a subset of the profile's tasks.
    // The snapshot is taken once per call and stays accurate: the only presence
    // this propagator ever changes is one it fixes to 0, and those were
    // undecided, so absent from the list to begin with.
    ReasonLiterals presence_lits;
    for (auto i : active_tasks)
        if (presence[i] && is_present(i))
            presence_lits.push_back(*presence[i] == 1_i);
    auto reason_with_presence = [&]() { return with_extra(generic_reason(reason_vars), presence_lits); };

    // Proof helper: pin task i's guaranteed load contribution at t and
    // return a (line, coeff) pair to feed the time-table pol. For a
    // constant height that is "active = 1" scaled by the height; for a
    // variable height it is "contrib >= lb(h_i)" with coefficient 1
    // (contrib is the proof-only product h_i·active in C_t). The
    // before/after RUPs give VeriPB the units to chase active's AND-gate.
    auto pin_contributor = [&](const ReasonLiterals & reason, size_t i, Integer t) -> std::pair<ProofLine, Integer> {
        auto fi = (t - per_task_t_lo[i]).raw_value;
        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * before_flags[i][fi] >= 1_i, ProofLevel::Temporary);
        // A mandatory task has s_i + l_i ≥ lb(s_i) + lb(l_i) > t.
        materialise_after_sum(i, state.lower_bound(starts[i]));
        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * after_flags[i][fi] >= 1_i, ProofLevel::Temporary);
        auto active_line = logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * active_flags[i][fi] >= 1_i, ProofLevel::Temporary);
        if (! h_is_var(i))
            return {active_line, hlb(i)};
        auto contrib_line = logger->emit_rup_proof_line_under_reason(reason, contrib_sum_of(contrib_flags[i][fi]) >= hlb(i), ProofLevel::Temporary);
        return {contrib_line, 1_i};
    };

    // The disjuncts a chain step's pins are weakened by --- what the step is out
    // to prove. An ordinary bound push carries the one literal saying the bound
    // has advanced; a presence falsification carries "task j is absent"
    // alongside it, so that every line the chain lays down reads "either the
    // bound has moved on, or the task is not there at all". At most two, so a
    // vector costs nothing worth avoiding on a path that only runs when a proof
    // is being written.
    // How many per-time flags a task has. Read from the windows rather than
    // from the flag vectors, which are empty when proofs are off --- the rule
    // has to clip its arithmetic to the same place either way, or it would
    // propagate differently depending on whether a proof was being written.
    auto active_flag_count = [&](size_t i) { return static_cast<size_t>((per_task_t_hi[i] - per_task_t_lo[i] + 1_i).raw_value); };

    // The window a task's flags actually reach, which is where the lemma clips
    // to. A task contained in [a, b) is contained in this too, and both its
    // guards have to be stated against it: a guard outside the clipped window
    // leaves survivors the derivation cannot weaken onto it, and each of those
    // costs a unit of the bound.
    auto clipped_window_start = [&](size_t i, Integer a) { return max(a, per_task_t_lo[i]); };
    auto clipped_window_end = [&](size_t i, Integer b) { return min(b, per_task_t_hi[i] + 1_i); };

    // Edge-finding's window-energy rows, derived once and cited after. The row
    // is a fact about the model --- the bounds a firing would have resolved its
    // leftover order literals against are carried as guard literals instead ---
    // so it lives at Top and outlives the search state that first wanted it.
    //
    // The length a variable-duration task is counted at is part of the key, and
    // has to be: it is the live lower bound, so the same task over the same
    // window is a different row once the search has tightened it. It is a guard
    // on the row too, which is what keeps the row itself a model fact.
    auto guarded_energy = [&](size_t i, Integer lo, Integer hi, Integer low_guard, Integer high_guard) -> const window_energy::GuardedWindowEnergy & {
        auto key = std::tuple{i, lo, hi, low_guard, high_guard, llb(i)};
        if (auto found = inputs.guarded_energy->find(key); found != inputs.guarded_energy->end())
            return found->second;
        auto derived = window_energy::derive_guarded_window_energy(*logger, lemma_task(i), lo, hi, low_guard, high_guard, ProofLevel::Top);
        if (! derived)
            throw ProofError{"cumulative edge-finding: task " + std::to_string(i) + " has no derivable window energy over [" +
                std::to_string(lo.raw_value) + "," + std::to_string(hi.raw_value) + ") guarded by [" + std::to_string(low_guard.raw_value) + "," +
                std::to_string(high_guard.raw_value) + ") (length " + std::to_string(llb(i).raw_value) + ", flags from " +
                std::to_string(per_task_t_lo[i].raw_value) + " for " + std::to_string(active_flags[i].size()) + ")"};
        return inputs.guarded_energy->emplace(key, *derived).first->second;
    };

    // Which of the pushed task's two guards its firing has to discharge. The
    // other one is the negated conclusion, and the wrapping RUP refutes it.
    enum class GuardToDischarge
    {
        Low,
        High
    };

    // Edge-finding's certificate, in both directions. It is the overload
    // check's, emitted under the negated conclusion: the contained tasks'
    // energy, plus what the pushed task must still occupy if the conclusion
    // were false, against the same capacity rows. That overflows the window, so
    // the pol is contradictory and the framework's wrapping RUP turns it into
    // the push.
    //
    // Every energy row is a *guarded* one, so it says nothing about the current
    // bounds and is cited rather than re-derived. What a firing pays is the
    // guard discharges and one pol.
    auto edge_finding_justification = [&](Integer a, Integer b, const vector<size_t> & inside_tasks, size_t pushed, Integer pushed_low_guard,
                                          Integer pushed_high_guard, GuardToDischarge discharge) {
        return [&, a, b, inside_tasks, pushed, pushed_low_guard, pushed_high_guard, discharge](const ReasonLiterals & reason) -> void {
            if (! logger)
                return;

            PolBuilder pol;
            for (Integer t = a; t < b; ++t) {
                if (std::holds_alternative<cumulative_proof_mutation::OmitCapacityLine>(mutation) && t == b - 1_i)
                    continue;
                if (auto line = capacity_lines.find(t); line != capacity_lines.end())
                    pol.add(line->second);
            }

            auto cite = [&](size_t i, Integer low_guard, Integer high_guard, bool discharge_low, bool discharge_high) {
                const auto & row = guarded_energy(i, a, b, low_guard, high_guard);
                pol.add(row.line, hlb(i));
                if (discharge_low && row.low_coeff > 0_i)
                    pol.add(
                        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (starts[i] >= row.low_guard) >= 1_i, ProofLevel::Temporary),
                        hlb(i) * row.low_coeff);
                if (discharge_high && row.bound > 0_i)
                    pol.add(
                        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (starts[i] < row.high_guard) >= 1_i, ProofLevel::Temporary),
                        hlb(i) * row.bound);
                // The length guard, which unlike the other two is discharged
                // whichever way the push goes: it says nothing about the
                // conclusion, only that the task really does run for as long as
                // the row counted it at. The reason carries every variable
                // length's bounds, so this closes on the same literals the row
                // was derived under.
                if (row.length_coeff > 0_i)
                    pol.add(logger->emit_rup_proof_line_under_reason(
                                reason, WPBSum{} + 1_i * (lengths_var[i] >= row.length_guard) >= 1_i, ProofLevel::Temporary),
                        hlb(i) * row.length_coeff);
            };

            // A contained task is inside the window whichever way the push
            // goes, so both its guards are refuted by the reason. Its high
            // guard is the first start that would take it out of the window,
            // stated against the *clipped* window since that is where the
            // lemma's sum stops; where the two differ the guard is refuted by
            // the task's declared bounds rather than by the search, and the RUP
            // closes on those just the same.
            for (auto i : inside_tasks) {
                if (std::holds_alternative<cumulative_proof_mutation::DropContainedTask>(mutation) && i == inside_tasks.front())
                    continue;
                cite(i, clipped_window_start(i, a), clipped_window_end(i, b) - llb(i) + 1_i, true, true);
            }

            // TTEF: the tasks the window does not contain still put their
            // mandatory-part load into it, and that load is pinned exactly the
            // way the overload check's (TTOC) strengthening pins it. A task
            // whose energy row is already in the pol must not be pinned as well
            // --- the capacity lines supply each time point once, so a second
            // claim on the same activity would leave the pol open.
            //
            // The bounds read here are the live ones rather than the mand_load
            // snapshot the sweep was set up from. A mandatory part only grows as
            // the sweep pushes bounds around, so the pins claim at least what
            // the firing's arithmetic counted, and a pol carrying more energy
            // than it needs closes just the same.
            if (rules.time_table_edge_finding) {
                vector<bool> contained(starts.size(), false);
                for (auto i : inside_tasks)
                    contained[i] = true;
                auto skip_pin = std::holds_alternative<cumulative_proof_mutation::DropProfilePin>(mutation);
                auto skip_all_pins = std::holds_alternative<cumulative_proof_mutation::DropProfilePins>(mutation);
                for (auto i : active_tasks) {
                    if (i == pushed || contained[i] || ! is_present(i))
                        continue;
                    auto lst = state.upper_bound(starts[i]);
                    auto eet = state.lower_bound(starts[i]) + llb(i);
                    for (Integer t = max(lst, a); t < min(eet, b); ++t) {
                        if (skip_all_pins)
                            continue;
                        if (skip_pin) {
                            skip_pin = false;
                            continue;
                        }
                        auto [line, coeff] = pin_contributor(reason, i, t);
                        pol.add(line, coeff);
                    }
                }
            }

            // No mutation lane for citing the pushed task's row at the
            // threshold a *contained* task would use, i.e. for forgetting to
            // clip. That was tried, and it verifies: the un-clipped row claims
            // more energy and is usually valid too, being the stronger claim.
            // So the clipping is not something a corrupted proof can be made to
            // reveal, and what keeps it honest is the propagator asking
            // window_energy_bound for exactly what the derivation will be given.
            cite(pushed, pushed_low_guard, pushed_high_guard, discharge == GuardToDischarge::Low, discharge == GuardToDischarge::High);

            pol.emit(*logger, ProofLevel::Temporary);
        };
    };

    using ExtLits = vector<IntegerVariableCondition>;

    auto plus_ext = [&](WPBSum sum, const ExtLits & ext, Integer coeff) -> WPBSum {
        for (const auto & e : ext)
            sum += coeff * e;
        return sum;
    };

    // Proof helper for the pushed task j, pinned under the EXTENDED
    // reason {reason ∧ ¬ext} (ext appended as disjuncts). For a constant
    // height it returns (active_j + Σext ≥ 1, h_j); for a variable height
    // it deposits contrib_j + lb(h_j)·Σext ≥ lb(h_j) (vacuous when some ext
    // literal holds, "contrib_j ≥ lb(h_j)" otherwise) and returns that line
    // with coefficient 1.
    auto pin_pushed = [&](const ReasonLiterals & reason, size_t j_idx, Integer t, const ExtLits & ext,
                          Integer s_lo_after) -> std::pair<ProofLine, Integer> {
        auto fj = (t - per_task_t_lo[j_idx]).raw_value;
        logger->emit_rup_proof_line_under_reason(reason, plus_ext(WPBSum{} + 1_i * before_flags[j_idx][fj], ext, 1_i) >= 1_i, ProofLevel::Temporary);
        // s_lo_after + lb(l_j) ≥ t+1 gives after_{j,t} = 1 (under ¬ext
        // for ub-push, under the running bound for lb-push).
        materialise_after_sum(j_idx, s_lo_after);
        logger->emit_rup_proof_line_under_reason(reason, plus_ext(WPBSum{} + 1_i * after_flags[j_idx][fj], ext, 1_i) >= 1_i, ProofLevel::Temporary);
        auto active_line = logger->emit_rup_proof_line_under_reason(
            reason, plus_ext(WPBSum{} + 1_i * active_flags[j_idx][fj], ext, 1_i) >= 1_i, ProofLevel::Temporary);
        if (! h_is_var(j_idx))
            return {active_line, hlb(j_idx)};
        auto contrib_line = logger->emit_rup_proof_line_under_reason(
            reason, plus_ext(contrib_sum_of(contrib_flags[j_idx][fj]), ext, hlb(j_idx)) >= hlb(j_idx), ProofLevel::Temporary);
        return {contrib_line, 1_i};
    };

    // Time-table consistency. The mandatory part of task i is the
    // half-open interval [lst_i, eet_i) where lst_i = ub(s_i) and
    // eet_i = lb(s_i) + l_i. Summing heights over mandatory parts
    // gives the load profile. Each task's bounds are then pushed
    // away from time points where placing it would force the load
    // over capacity.

    // Determine the time window we care about: the union of every
    // task's possibly-active range. This bounds both the mandatory
    // profile and the per-task bound search.
    bool any = false;
    Integer t_lo = 0_i, t_hi = -1_i;
    for (auto i : active_tasks) {
        if (is_absent(i))
            continue;
        auto [s_lo, s_hi] = state.bounds(starts[i]);
        auto lo = s_lo, hi = s_hi + lub(i) - 1_i;
        if (! any || lo < t_lo)
            t_lo = lo;
        if (! any || hi > t_hi)
            t_hi = hi;
        any = true;
    }
    if (! any)
        return PropagatorState::DisableUntilBacktrack;

    auto range = (t_hi - t_lo + 1_i).raw_value;
    vector<Integer> mand_load(range, 0_i);

    // Only tasks known present have a mandatory part: an undecided one might
    // not be scheduled at all, so none of its resource use is guaranteed.
    for (auto i : active_tasks) {
        if (! is_present(i))
            continue;
        auto lst = state.upper_bound(starts[i]);
        auto eet = state.lower_bound(starts[i]) + llb(i);
        if (lst < eet)
            for (Integer t = lst; t < eet; ++t)
                mand_load[(t - t_lo).raw_value] += hlb(i);
    }

    for (auto idx = 0; rules.time_table && idx < range; ++idx)
        if (mand_load[idx] > capacity) {
            auto violating_t = t_lo + Integer{idx};

            // Tasks whose mandatory part covers violating_t — the ones
            // we'll pin to active=1 in the proof.
            vector<size_t> contributing;
            for (auto i : active_tasks) {
                if (! is_present(i))
                    continue;
                auto lst = state.upper_bound(starts[i]);
                auto eet = state.lower_bound(starts[i]) + llb(i);
                if (lst < eet && violating_t >= lst && violating_t < eet)
                    contributing.push_back(i);
            }

            auto justify = [&, violating_t, contributing](const ReasonLiterals & reason) -> void {
                if (! logger)
                    return;
                // Pin every contributing task's guaranteed load at
                // violating_t, then combine those lines with C_t in a
                // single pol. The result is unsatisfiable under the
                // reason context (the pinned loads already exceed
                // ub(capacity)), closing the framework's wrapping RUP.
                PolBuilder pol;
                pol.add(capacity_lines.at(violating_t));
                for (auto i : contributing) {
                    auto [line, coeff] = pin_contributor(reason, i, violating_t);
                    pol.add(line, coeff);
                }
                pol.emit(*logger, ProofLevel::Temporary);
            };

            inference.contradiction(logger, JustifyExplicitly{justify, ThenRUP::Yes, hints::Cumulative{owner}}, reason_with_presence());
            return PropagatorState::DisableUntilBacktrack;
        }

    // Overload checking: rule (OC') of Cloutier & Quimper, CP 2026,
    // strengthened by the mandatory-part profile to their (TTOC). If
    // the tasks that must run entirely inside a time window carry more
    // energy than the window can supply, the constraint is infeasible.
    // This is conflict-only --- no bound moves --- so a bug here shows
    // up as a missing solution, which is what the enumeration tests
    // are the net for.
    //
    // The windows worth trying are [a, b) with a an earliest start and
    // b a latest completion time. I(a, b), the tasks with est >= a and
    // lct <= b, contribute their whole energy p·h; every other task
    // contributes whatever of its mandatory part falls inside the
    // window. A task in I(a, b) has its mandatory part inside the
    // window as well, so that second term is the window's total
    // mandatory load minus I(a, b)'s --- which makes both terms
    // accumulate as b grows, and the whole sweep quadratic.
    //
    // Two restrictions, both of which only weaken the check: the
    // capacity must be constant (a variable one would leave a
    // (b − a)·capacity term in the conflict pol for the wrapping RUP
    // to dispose of over the capacity's bits, which it cannot do in
    // general), and only eligible tasks (see prepare_overload_check)
    // may join I(a, b).
    if (rules.overload && ! overload_tasks.empty() && is_constant_variable(capacity_var)) {
        vector<Integer> mand_prefix(static_cast<size_t>(range) + 1, 0_i);
        for (auto idx = 0; idx < range; ++idx)
            mand_prefix[static_cast<size_t>(idx) + 1] = mand_prefix[static_cast<size_t>(idx)] + mand_load[static_cast<size_t>(idx)];

        // Mandatory load inside [from, to), over every task.
        auto profile_within = [&](Integer from, Integer to) {
            return mand_prefix[static_cast<size_t>((to - t_lo).raw_value)] - mand_prefix[static_cast<size_t>((from - t_lo).raw_value)];
        };

        // How many time points in [from, to) some task can occupy.
        // Anywhere else supplies nothing to this window's tasks (and
        // has no capacity line to cite), so it is not counted.
        auto slots_within = [&](Integer from, Integer to) {
            return time_slot_prefix[static_cast<size_t>((to - time_slot_lo).raw_value)] -
                time_slot_prefix[static_cast<size_t>((from - time_slot_lo).raw_value)];
        };

        struct Candidate
        {
            size_t task;
            Integer est, lct, energy, mandatory;
            // Kept alongside the energy they multiply out to, so that
            // edge-finding's scan reads them rather than asking the state again
            // for every window it looks at.
            Integer length, height;
        };

        vector<Candidate> candidates;
        candidates.reserve(overload_tasks.size());
        for (auto i : overload_tasks) {
            // An optional task carries guaranteed energy only once it is known
            // present. Until then it might not be scheduled at all, and
            // counting its energy would manufacture a conflict that is not
            // there. Its presence literal is already in the reason, put there
            // with every other known-present task's.
            if (! is_present(i))
                continue;
            // A task guaranteed no duration at all carries no guaranteed
            // energy, so there is nothing for the lemma to establish and
            // nothing for the window to be charged. Only reachable for a
            // variable length --- a constant one this small was turned away at
            // prepare time --- and it can stop being true further down the
            // search, which is why it is asked here and not there.
            if (llb(i) <= 0_i)
                continue;
            auto [s_lo, s_hi] = state.bounds(starts[i]);
            auto p = llb(i), h = hlb(i);
            candidates.push_back(Candidate{i, s_lo, s_hi + p, p * h, h * max(0_i, s_lo + p - s_hi), p, h});
        }
        // An empty candidate list leaves window_starts empty too, so the window
        // loop below simply does not run; no early exit needed.
        sort(candidates, [](const Candidate & a, const Candidate & b) { return a.lct < b.lct; });

        // Edge-finding's `rest` is monotone in the pushed task's height and in
        // nothing else about it, so walking the candidates tallest-first lets
        // the scan stop at the first task that cannot be pushed instead of
        // running to the end. That is what keeps the rule from turning the
        // overload check's quadratic sweep cubic: most windows stop on the
        // first task, and the `tallest` guard below is that first test hoisted
        // out of the loop entirely.
        vector<size_t> by_height;
        Integer tallest = 0_i, heaviest = 0_i;
        if (rules.edge_finding) {
            by_height.resize(candidates.size());
            for (size_t i = 0; i < candidates.size(); ++i)
                by_height[i] = i;
            sort(by_height, [&](size_t x, size_t y) { return candidates[x].height > candidates[y].height; });
            if (! candidates.empty())
                tallest = candidates[by_height.front()].height;
            // Detection needs some task's whole energy to overflow the window
            // alongside the contained ones, so the largest single task energy
            // rules a window out for every task at once, exactly as `tallest`
            // does for `rest`. One more multiplication, and it is free.
            for (const auto & c : candidates)
                heaviest = max(heaviest, c.energy);
        }

        vector<Integer> window_starts;
        window_starts.reserve(candidates.size());
        for (const auto & c : candidates)
            window_starts.push_back(c.est);
        sort(window_starts);

        // (TTHE-OC) and (KAOC) charge the window one time point at a time, so
        // they need to know what the contained set could take at each of them
        // separately. Two arrays indexed by t − t_lo carry it: the heights of
        // the contained tasks that could run at t without being compulsory
        // there, and — for the knapsack rule — which totals those heights can
        // actually add up to, as a bitset over 0..capacity.
        //
        // Both are grown one task at a time as the window's right edge
        // advances and reset when the left edge moves, which is Cloutier &
        // Quimper's incremental Profile (their Algorithm 3 is the shift-or on
        // the bitset). Their doubly linked list over time points is the part
        // not reproduced here: it collapses runs where the profile is constant,
        // and without it this sweep is O(n²·horizon) rather than O(Cn²). That
        // is the same trade #742 records for edge-finding's scan, and the same
        // answer — the rule is off by default, and the cost is propagation
        // performance rather than proof content.
        //
        // A variable height would put bit-linearised contribution terms in the
        // capacity line instead of one `h·active`, which neither the knapsack's
        // item list nor the term-dropping below can read. v1 declines rather
        // than approximates: the plain rules above still run.
        auto elastic_rules = (rules.elastic_overload || rules.knapsack_overload) && none_of(active_tasks, [&](size_t i) { return h_is_var(i); });

        // The knapsack cap is pseudo-polynomial in the capacity twice over: a
        // bitset of `capacity + 1` bits at every time point, and a layer of
        // proof flags per reachable partial sum in every strengthening it
        // certifies. Scheduling capacities are small --- Cloutier & Quimper
        // report C <= 122 across their benchmarks, and the local RCPSP
        // instances run 5 to 22 --- so this bound is far above anything the
        // rule is meant for, and exists so that a model with a capacity in the
        // millions degrades to the horizontally elastic cap instead of asking
        // for terabytes. Not a silent cap on strength: what it turns off is one
        // of three rungs, and the two below it still run.
        constexpr auto max_knapsack_capacity = 4096;
        auto knapsack_rule = rules.knapsack_overload && capacity <= Integer{max_knapsack_capacity};
        auto knapsack_words = static_cast<size_t>(capacity.raw_value / 64 + 1);
        vector<Integer> optional_height(elastic_rules ? static_cast<size_t>(range) : 0, 0_i);
        vector<uint64_t> reachable(elastic_rules && knapsack_rule ? static_cast<size_t>(range) * knapsack_words : 0, 0);

        // The times this task is optional at: it could be running, but nothing
        // says it must be. Its compulsory part is charged to the profile
        // instead, and comes off the *required* side of the comparison rather
        // than off what the time point supplies --- so counting it here as well
        // would charge it twice, and the pol would not close.
        //
        // A task with no compulsory part at all is optional across the whole of
        // [est, lct), which is the case to be careful with: `lst` is then at or
        // past `ect`, and taking the two ends as [est, lst) and [ect, lct)
        // would silently drop everything between them.
        auto optional_times = [&](const Candidate & c) {
            auto lst = c.lct - c.length, ect = c.est + c.length;
            if (lst < ect)
                return pair{pair{c.est, lst}, pair{ect, c.lct}};
            return pair{pair{c.est, c.lct}, pair{c.lct, c.lct}};
        };

        auto join_elastic = [&](const Candidate & c) {
            auto [before, after] = optional_times(c);
            for (auto [from, to] : {before, after})
                for (Integer t = from; t < to; ++t) {
                    auto idx = static_cast<size_t>((t - t_lo).raw_value);
                    optional_height[idx] += c.height;
                    if (knapsack_rule) {
                        // bitset |= bitset << height, most significant word
                        // first so a shift reads only bits it has not written.
                        auto * bits = reachable.data() + idx * knapsack_words;
                        auto shift = static_cast<size_t>(c.height.raw_value);
                        for (size_t k = knapsack_words; k-- > 0;) {
                            auto word = (shift / 64 > k) ? 0ull : bits[k - shift / 64] << (shift % 64);
                            if (shift % 64 != 0 && shift / 64 < k)
                                word |= bits[k - shift / 64 - 1] >> (64 - shift % 64);
                            bits[k] |= word;
                        }
                    }
                }
        };

        // What one time point supplies to the contained set: what the profile
        // leaves of the capacity, capped by what the tasks that could be here
        // are between them able to take — and, for (KAOC), by the largest total
        // those heights can actually add up to, since a resource no subset of
        // them can reach is not available either.
        auto elastic_supply_at = [&](Integer t) {
            auto idx = static_cast<size_t>((t - t_lo).raw_value);
            auto left = max(0_i, capacity - mand_load[idx]);
            auto cap = min(left, optional_height[idx]);
            if (knapsack_rule && cap > 0_i) {
                const auto * bits = reachable.data() + idx * knapsack_words;
                for (Integer v = cap; v >= 0_i; --v)
                    if (bits[static_cast<size_t>(v.raw_value) / 64] >> (static_cast<size_t>(v.raw_value) % 64) & 1ull)
                        return v;
                return 0_i;
            }
            return cap;
        };

        for (size_t w = 0; w < window_starts.size(); ++w) {
            if (w > 0 && window_starts[w] == window_starts[w - 1])
                continue;
            auto a = window_starts[w];

            if (elastic_rules) {
                fill(optional_height, 0_i);
                fill(reachable, 0ull);
                // Every bitset starts with only the empty subset reachable.
                for (size_t k = 0; k < reachable.size(); k += knapsack_words)
                    reachable[k] = 1ull;
            }

            // min_ect and max_lst are not-first / not-last's thresholds, over
            // the same growing contained set the energy accumulates over.
            Integer energy = 0_i, inside_mandatory = 0_i, min_ect = 0_i, max_lst = 0_i;
            vector<size_t> inside_tasks;
            for (const auto & c : candidates) {
                if (c.est < a)
                    continue;
                energy += c.energy;
                inside_mandatory += c.mandatory;
                inside_tasks.push_back(c.task);
                if (elastic_rules)
                    join_elastic(c);
                min_ect = inside_tasks.size() == 1 ? c.est + c.length : min(min_ect, c.est + c.length);
                max_lst = inside_tasks.size() == 1 ? c.lct - c.length : max(max_lst, c.lct - c.length);

                auto b = c.lct;
                auto width = slots_within(a, b);
                auto supply = capacity * width;

                // The mandatory-part load of the tasks that are *not* contained
                // in the window: what (TTOC) adds to the overload check below,
                // and what TTEF adds to edge-finding. A contained task's
                // mandatory part lies inside the window too, so taking I(a, b)'s
                // off the window's total leaves exactly the rest.
                auto window_profile = profile_within(a, b) - inside_mandatory;

                // A task's *guaranteed* energy inside the window: the least
                // overlap its execution interval can have with [a, b) over the
                // starts its bounds still allow. This is one call of the very
                // lemma a certificate would cite, and it is at least the task's
                // mandatory part in the window --- and for a contained task it
                // is the whole of its energy.
                //
                // A task the window cannot reach has a *negative* bound here,
                // the lemma's way of saying it has more slack than the window
                // has room, so clamp before summing.
                auto guaranteed = [&](const Candidate & c2) {
                    return c2.height *
                        max(0_i,
                            window_energy::window_energy_bound(
                                c2.length, per_task_t_lo[c2.task], active_flag_count(c2.task), a, b, pair{c2.est, c2.lct - c2.length}));
                };

                // What the window is charged with, before the task being pushed
                // is taken back out of it:
                //
                //   edge-finding  the contained tasks' whole energy
                //   TTEF          plus the mandatory-part load of the rest
                //   energetic     every task's guaranteed energy, which
                //                 subsumes both
                Integer window_total = energy;
                if (rules.energetic_edge_finding) {
                    window_total = 0_i;
                    for (const auto & c2 : candidates)
                        window_total += guaranteed(c2);
                }
                else if (rules.time_table_edge_finding)
                    window_total = energy + window_profile;

                // Whatever of a task the window has already been charged with.
                // A push adds that task's clipped energy under the negated
                // conclusion, covering the same time points, and each time
                // point has one capacity line to cancel against --- so this
                // comes back out first, or the pol would be left open.
                // lst = lct − p and eet = est + p, which is what mand_load was
                // built from.
                auto own_contribution = [&](const Candidate & c2) {
                    return rules.energetic_edge_finding ? guaranteed(c2)
                        : rules.time_table_edge_finding ? c2.height * max(0_i, min(c2.est + c2.length, b) - max(c2.lct - c2.length, a))
                                                        : 0_i;
                };

                // Edge-finding. A task j that starts inside [a, b) but is not
                // contained in it can be pushed when the window has no room
                // left: if everything contained plus the whole of j cannot fit,
                // j must end after b, and the most of j that can be inside the
                // window is what the contained tasks leave over. Writing
                //
                //     rest = energy − (capacity − h_j) · width
                //
                // for the contained energy that exceeds what could be there if
                // j ran at full height across the whole window, j occupies at
                // most width − ⌈rest / h_j⌉ of the window's slots, so it starts
                // at a + ⌈rest / h_j⌉ or later.
                //
                // The rule is written to fit one certificate: over this window,
                // the contained tasks' energy by the window-energy lemma, plus
                // j's *clipped* energy at start bounds [est_j, new_lb − 1],
                // against the same capacity lines the overload check cites.
                // Which is why the fire condition below is the certificate's
                // own inequality and not the textbook detection alone --- what
                // the propagator asks is exactly what the proof will say.
                // `window_total <= supply` because a window that already
                // overflows is a conflict, not a push: the overload check below
                // owns it, and edge-finding's arithmetic there yields a `rest`
                // big enough to put new_lb past the window entirely, where the
                // pushed task's clipped energy is zero and there is nothing to
                // certify with. (Which is why the strengthened forms want
                // profile_overload on: with it off, a window only the extra
                // energy overloads is skipped here and refuted nowhere. Sound,
                // just weaker.)
                //
                // All three tests charge the window in full, so they stay
                // necessary conditions for a firing once the pushed task's own
                // contribution comes back out below.
                if (rules.edge_finding && ! inside_tasks.empty() && window_total <= supply && window_total > (capacity - tallest) * width &&
                    window_total + heaviest > supply) {
                    // One pass for both directions. They share everything up to
                    // the last test --- the same candidates in the same order,
                    // the same `rest`, the same detection --- and differ only in
                    // which side of the window the pushed task hangs off. Two
                    // passes walked the same prefix twice for nothing, and the
                    // scan is where this rule's whole cost is.
                    for (auto j_idx : by_height) {
                        const auto & j = candidates[j_idx];

                        // Heights descend, so once one task's `rest` has gone
                        // non-positive every shorter one's has too. Test the
                        // figure that charges the window in full here: taking
                        // j's own contribution back out below only lowers
                        // `rest`, so the early exit stays valid.
                        auto h_j = j.height;
                        if (window_total - (capacity - h_j) * width <= 0_i)
                            break;

                        // A task with one end inside the window and one outside.
                        // Both ends in means it is contained, and already
                        // counted; neither means it spans the window, where the
                        // closed form below does not apply --- that case is what
                        // not-first / not-last is for. Which end is in decides
                        // which bound moves.
                        auto starts_inside = j.est >= a, ends_inside = j.lct <= b;
                        if (starts_inside == ends_inside)
                            continue;

                        auto p_j = j.length;

                        auto other_energy = window_total - own_contribution(j);
                        auto rest = other_energy - (capacity - h_j) * width;
                        if (rest <= 0_i)
                            continue;

                        // Detection: everything else in the window together with
                        // the whole of j does not fit. Without it the push can
                        // land where j's clipped energy is only p_j, which is too
                        // little to refute.
                        if (other_energy + h_j * p_j <= supply)
                            continue;

                        // Against the live bound, not the snapshot this sweep
                        // was set up from: an earlier window in the same sweep
                        // may already have pushed this task past here, and
                        // re-inferring a bound that is already held costs a
                        // whole certificate for nothing. Worth 2x the firings
                        // on a real instance.
                        //
                        // The clipped energy is then asked for over exactly the
                        // start bounds the guarded derivation will be given ---
                        // the row is a model fact, and asking for anything else
                        // would let the rule fire on more energy than the
                        // certificate establishes --- and over j's real flag
                        // range, because a window can run past the last time a
                        // task could be active and the lemma clips there.
                        auto step = (rest + h_j - 1_i) / h_j;
                        auto low_guard = starts_inside ? clipped_window_start(j.task, a) : b - p_j - step + 1_i;
                        auto high_guard = starts_inside ? a + step : clipped_window_end(j.task, b) - p_j + 1_i;

                        if (starts_inside ? high_guard <= state.lower_bound(starts[j.task]) : low_guard - 1_i >= state.upper_bound(starts[j.task]))
                            continue;

                        auto clipped = window_energy::window_energy_bound(
                            p_j, per_task_t_lo[j.task], active_flag_count(j.task), a, b, pair{low_guard, high_guard - 1_i});
                        if (clipped <= 0_i || other_energy + h_j * clipped <= supply)
                            continue;

                        auto one_too_far = std::holds_alternative<cumulative_proof_mutation::PushOneTooFar>(mutation);
                        auto justify = edge_finding_justification(
                            a, b, inside_tasks, j.task, low_guard, high_guard, starts_inside ? GuardToDischarge::Low : GuardToDischarge::High);
                        if (starts_inside) {
                            inference.infer_greater_than_or_equal(logger, starts[j.task], one_too_far ? high_guard + 1_i : high_guard,
                                JustifyExplicitly{justify, ThenRUP::Yes, hints::Cumulative{owner}}, reason_with_presence());
                        }
                        else {
                            inference.infer_less_than(logger, starts[j.task], one_too_far ? low_guard - 1_i : low_guard,
                                JustifyExplicitly{justify, ThenRUP::Yes, hints::Cumulative{owner}}, reason_with_presence());
                        }
                    }
                }

                // Not-first / not-last. Edge-finding asks how far a task can be
                // pushed and answers with a closed form; this asks a different
                // question --- can j start before every task the window
                // contains has finished, or end after every one of them has
                // started --- and takes its thresholds from the contained set
                // rather than from the leftover energy.
                //
                // Where j has one end inside the window the two overlap, and
                // edge-finding's threshold is the furthest an energy argument
                // over this window can reach, so its push subsumes this one and
                // the live-bound tests below drop the duplicate. What is new is
                // a j that SPANS the window: its guaranteed energy is a hump in
                // its start, edge-finding's closed form assumes a task crossing
                // one edge and so does not apply, and the rule above skips it.
                // Restricting the start to one side of a threshold is exactly
                // what makes the hump's minimum say something.
                if (rules.not_first_not_last && ! inside_tasks.empty() && window_total <= supply) {
                    for (const auto & j : candidates) {
                        if (j.est >= a && j.lct <= b)
                            continue;

                        auto h_j = j.height, p_j = j.length;
                        auto other_energy = window_total - own_contribution(j);
                        auto [s_lo, s_hi] = state.bounds(starts[j.task]);

                        // Not-first: refute "j starts before every contained
                        // task has ended". The guarded row's low guard is what
                        // the reason discharges and its high guard is the
                        // threshold, which is the negated conclusion.
                        //
                        // Any low guard at or past the window's start discharges
                        // every survivor the ladder has, so where j's own lower
                        // bound is inside the window the window's start does
                        // just as well --- and it is a fact about the window
                        // rather than about the search, so the row it derives is
                        // shared with edge-finding's rather than keyed on a
                        // bound that moves.
                        if (min_ect > s_lo) {
                            auto low_guard = min(s_lo, clipped_window_start(j.task, a));
                            auto clipped = window_energy::window_energy_bound(
                                p_j, per_task_t_lo[j.task], active_flag_count(j.task), a, b, pair{low_guard, min_ect - 1_i});
                            if (clipped > 0_i && other_energy + h_j * clipped > supply) {
                                auto one_too_far = std::holds_alternative<cumulative_proof_mutation::PushOneTooFar>(mutation);
                                auto justify = edge_finding_justification(a, b, inside_tasks, j.task, low_guard, min_ect, GuardToDischarge::Low);
                                inference.infer_greater_than_or_equal(logger, starts[j.task], one_too_far ? min_ect + 1_i : min_ect,
                                    JustifyExplicitly{justify, ThenRUP::Yes, hints::Cumulative{owner}}, reason_with_presence());
                            }
                        }

                        // Not-last: the mirror. Refute "j ends after every
                        // contained task has started", so the negated conclusion
                        // lands on the low guard and j's own upper bound is what
                        // the reason discharges.
                        if (max_lst - p_j < s_hi) {
                            auto low_guard = max_lst - p_j + 1_i;
                            auto clipped = window_energy::window_energy_bound(
                                p_j, per_task_t_lo[j.task], active_flag_count(j.task), a, b, pair{low_guard, s_hi});
                            if (clipped > 0_i && other_energy + h_j * clipped > supply) {
                                auto one_too_far = std::holds_alternative<cumulative_proof_mutation::PushOneTooFar>(mutation);
                                auto justify = edge_finding_justification(a, b, inside_tasks, j.task, low_guard, s_hi + 1_i, GuardToDischarge::High);
                                inference.infer_less_than(logger, starts[j.task], one_too_far ? low_guard - 1_i : low_guard,
                                    JustifyExplicitly{justify, ThenRUP::Yes, hints::Cumulative{owner}}, reason_with_presence());
                            }
                        }
                    }
                }

                auto outside_profile = rules.profile_overload ? window_profile : 0_i;

                // (TTHE-OC) and (KAOC). Both compare the same two quantities,
                // and differ only in how tightly one of them is capped:
                //
                //   required   each contained task's energy, less whatever of
                //              it its compulsory part already accounts for
                //   supplied   summed one time point at a time, each capped by
                //              what the profile leaves, by the heights of the
                //              tasks that could be there, and (KAOC) by the
                //              largest total those heights can reach
                //
                // With no cap but the profile's this is exactly (TTOC): each
                // contained task's compulsory load comes off the required side
                // and goes back on as the supply the profile removes, and the
                // two rearrange into `e + F > C·(b−a)` term for term. So the
                // rules form a ladder over one comparison, and the certificate
                // below is one shape with a tighter line per time point --- not
                // three certificates.
                //
                // Tried only where (TTOC) has already declined, which is sound
                // because it dominates neither: whatever (TTOC) detects, this
                // detects too. What that buys is the cheaper certificate
                // wherever the cheaper rule was enough.
                if (elastic_rules && ! inside_tasks.empty() && energy + outside_profile <= supply) {
                    auto required = energy - inside_mandatory;

                    // What each time point supplies with and without the
                    // knapsack cap. The gap between them is what strengthening
                    // that point would buy the conflict, and it is worth
                    // knowing separately: the DP costs a layer of proof flags
                    // per reachable partial sum, so the certificate pays for it
                    // only where the contradiction cannot do without.
                    Integer elastic_total = 0_i;
                    vector<pair<Integer, Integer>> gain_at;
                    for (Integer t = a; t < b; ++t) {
                        auto idx = static_cast<size_t>((t - t_lo).raw_value);
                        auto uncapped = min(max(0_i, capacity - mand_load[idx]), optional_height[idx]);
                        elastic_total += uncapped;
                        if (auto gain = uncapped - elastic_supply_at(t); gain > 0_i)
                            gain_at.emplace_back(gain, t);
                    }

                    // Biggest gains first, and stop as soon as the comparison
                    // tips: `strengthen` is then exactly the set of time points
                    // the conflict rests on, and every other one keeps the
                    // cheap line.
                    sort(gain_at, [](const auto & x, const auto & y) { return x.first > y.first; });
                    vector<Integer> strengthen;
                    auto supplied = elastic_total;
                    for (const auto & [gain, t] : gain_at) {
                        if (required > supplied)
                            break;
                        supplied -= gain;
                        strengthen.push_back(t);
                    }

                    if (required > supplied) {
                        auto justify = [&, a, b, inside_tasks, strengthen, required, supplied](const ReasonLiterals & reason) -> void {
                            Integer pol_supply = 0_i, pol_required = 0_i;
                            if (! logger)
                                return;
                            logger->emit_proof_comment("cumulative overload conflict window=[" + std::to_string(a.raw_value) + "," +
                                std::to_string(b.raw_value) + ") rule=" + (strengthen.empty() ? "ttheoc" : "kaoc") +
                                " strengthened=" + std::to_string(strengthen.size()) + "/" + std::to_string((b - a).raw_value));

                            // Tests only: each of these breaks one step of what
                            // follows in a way that must make VeriPB reject.
                            // See CumulativeProofMutation.
                            auto claim_one_better = std::holds_alternative<cumulative_proof_mutation::ClaimOneBetterAvailability>(mutation);
                            auto strengthen_one_fewer = std::holds_alternative<cumulative_proof_mutation::StrengthenOneFewer>(mutation);
                            auto omit_capacity_line = std::holds_alternative<cumulative_proof_mutation::OmitCapacityLine>(mutation);

                            vector<bool> is_inside(starts.size(), false);
                            for (auto i : inside_tasks)
                                is_inside[i] = true;

                            PolBuilder pol;

                            // One availability line per time point: the
                            // capacity row, with every compulsory contribution
                            // pinned off it and every term that is not a
                            // contained task's optional one weakened away, so
                            // that what is left is a statement about exactly
                            // the heights the knapsack reasons over.
                            for (Integer t = a; t < b; ++t) {
                                if (omit_capacity_line && t == b - 1_i)
                                    continue;
                                auto capacity_line = capacity_lines.find(t);
                                if (capacity_line == capacity_lines.end())
                                    continue;

                                auto idx = static_cast<size_t>((t - t_lo).raw_value);
                                auto left = max(0_i, capacity - mand_load[idx]);

                                // Which of the contained tasks could be running
                                // here without being obliged to. These are the
                                // heights the cap is stated over, whichever way
                                // it is derived.
                                vector<SubsetSumItem> items;
                                for (auto j : active_tasks) {
                                    if (t < per_task_t_lo[j] || t > per_task_t_hi[j] || ! is_inside[j])
                                        continue;
                                    auto lst = state.upper_bound(starts[j]), eet = state.lower_bound(starts[j]) + llb(j);
                                    if (is_present(j) && lst <= t && t < eet)
                                        continue;
                                    if (state.lower_bound(starts[j]) <= t && t < state.upper_bound(starts[j]) + llb(j))
                                        items.push_back(
                                            SubsetSumItem{hlb(j), active_flags[j][static_cast<size_t>((t - per_task_t_lo[j]).raw_value)]});
                                }

                                // Where those heights do not add up to what the
                                // profile leaves, the capacity row is not the
                                // binding fact and citing it would supply the
                                // window with resource nobody can take. The
                                // binding fact is then each task's own literal
                                // axiom, and their sum is the whole cap --- no
                                // capacity row, no pins, and nothing for the
                                // knapsack to improve on, since the entire set
                                // already fits.
                                //
                                // This is the horizontally elastic cap, and
                                // deriving it rather than only computing it is
                                // what the first version got wrong: a fixture
                                // where every task can be at every time point
                                // never takes this branch, and every published
                                // one is like that.
                                if (optional_height[idx] <= left) {
                                    pol_supply += optional_height[idx];
                                    for (const auto & item : items)
                                        pol.add(! logger->names_and_ids_tracker().xliteral_for(std::get<ProofFlag>(item.term)), item.coefficient,
                                            logger->names_and_ids_tracker());
                                    continue;
                                }

                                PolBuilder avail;
                                avail.add(capacity_line->second);
                                for (auto j : active_tasks) {
                                    if (t < per_task_t_lo[j] || t > per_task_t_hi[j])
                                        continue;
                                    auto flag = active_flags[j][static_cast<size_t>((t - per_task_t_lo[j]).raw_value)];
                                    auto lst = state.upper_bound(starts[j]), eet = state.lower_bound(starts[j]) + llb(j);
                                    if (is_present(j) && lst <= t && t < eet) {
                                        auto [line, coeff] = pin_contributor(reason, j, t);
                                        avail.add(line, coeff);
                                    }
                                    else if (! (is_inside[j] && state.lower_bound(starts[j]) <= t && t < state.upper_bound(starts[j]) + llb(j)))
                                        avail.weaken(flag, logger->names_and_ids_tracker());
                                }

                                auto line = avail.emit(*logger, ProofLevel::Temporary);
                                auto strengthen_here = find(strengthen, t) != strengthen.end();
                                if (strengthen_one_fewer && ! strengthen.empty() && t == strengthen.front())
                                    strengthen_here = false;
                                if (strengthen_here) {
                                    // The reason goes in: the availability
                                    // line was derived under it (its pins
                                    // carry the negated reason's literals
                                    // alongside their own terms), so a dead
                                    // state's "this prefix cannot be
                                    // completed" only holds where the reason
                                    // does, and every RUP inside the
                                    // strengthening has to say so too.
                                    auto strengthened = derive_subset_sum_strengthening(*logger, items, line, left, ProofLevel::Temporary, reason,
                                        claim_one_better ? SubsetSumMutation{subset_sum_mutation::ClaimOneBetter{}}
                                                         : SubsetSumMutation{subset_sum_mutation::None{}});
                                    if (! claim_one_better && strengthened.bound != elastic_supply_at(t))
                                        throw ProofError{"cumulative knapsack overload: the strengthening at time " + std::to_string(t.raw_value) +
                                            " reached " + std::to_string(strengthened.bound.raw_value) + ", not the " +
                                            std::to_string(elastic_supply_at(t).raw_value) + " the check counted on"};
                                    line = strengthened.line;
                                    pol_supply += strengthened.bound;
                                }
                                else
                                    pol_supply += left;
                                pol.add(line);
                            }

                            // ... against each contained task's energy, with
                            // its compulsory times weakened back out of the
                            // sum: those time points charged the availability
                            // side instead, and counting them twice would leave
                            // the pol open.
                            //
                            // That weakening is what makes the pol *itself*
                            // contradictory, and it is deliberately kept even
                            // though it is not load-bearing: leaving it out
                            // still verifies, because the terms it would have
                            // cancelled are ones unit propagation assigns from
                            // the reason's own bound literals --- the same
                            // reason (TTOC)'s pins are usually droppable. So
                            // there is no mutation lane for this step; a
                            // corruption of it is accepted, and rightly.
                            for (auto i : inside_tasks) {
                                // Over the task's *own* [est, lct), not over
                                // the whole window. A contained task's span
                                // sits inside the window either way, so the
                                // bound is the same p_i --- but the sum's time
                                // points then line up exactly with the ones the
                                // availability lines charged for.
                                //
                                // Take the window instead and the pol is left
                                // with a negative coefficient on every
                                // (task, time) the task cannot reach: the
                                // availability lines never mention those, and
                                // nothing cancels them. Unit propagation
                                // usually finishes it from the reason's bound
                                // literals, which is why every fixture where
                                // the tasks all span the window verifies
                                // anyway, and why this only showed up on
                                // generated instances.
                                auto [i_est, i_lst] = state.bounds(starts[i]);
                                auto energy_line = window_energy::derive_window_energy(
                                    *logger, reason, lemma_task(i), i_est, i_lst + llb(i), state.bounds(starts[i]), ProofLevel::Temporary);
                                if (! energy_line || energy_line->bound != llb(i))
                                    throw ProofError{"cumulative elastic overload: a contained task's window energy is not its whole length"};
                                pol.add(energy_line->line, hlb(i));
                                pol_required += hlb(i) * energy_line->bound;

                                auto lst = state.upper_bound(starts[i]), eet = state.lower_bound(starts[i]) + llb(i);
                                for (Integer t = max(lst, a); t < min(eet, b); ++t) {
                                    pol.add(! logger->names_and_ids_tracker().xliteral_for(
                                                active_flags[i][static_cast<size_t>((t - per_task_t_lo[i]).raw_value)]),
                                        hlb(i), logger->names_and_ids_tracker());
                                    pol_required -= hlb(i);
                                }
                            }

                            // What the pol actually adds up to, against what
                            // the rule decided to fire on. The two are computed
                            // on opposite sides of the propagator --- one from
                            // the incremental per-time-point arrays, the other
                            // from the lines as they are emitted --- so they
                            // agree only if the certificate is charging the
                            // window for what the check counted. A mismatch is
                            // a proof VeriPB will reject, and it reads far
                            // better here than there. Off under a mutation,
                            // whose whole purpose is to make the two disagree.
                            if (std::holds_alternative<cumulative_proof_mutation::None>(mutation) &&
                                (pol_supply != supplied || pol_required != required))
                                throw ProofError{"cumulative elastic overload: the pol says " + std::to_string(pol_required.raw_value) + " > " +
                                    std::to_string(pol_supply.raw_value) + " but the check said " + std::to_string(required.raw_value) + " > " +
                                    std::to_string(supplied.raw_value) + " over [" + std::to_string(a.raw_value) + "," + std::to_string(b.raw_value) +
                                    ")"};

                            pol.emit(*logger, ProofLevel::Temporary);
                        };

                        inference.contradiction(
                            logger, JustifyExplicitly{justify, ThenRUP::Yes, hints::CumulativeOverload{owner}}, reason_with_presence());
                        return PropagatorState::DisableUntilBacktrack;
                    }
                }

                if (energy + outside_profile <= supply)
                    continue;

                // (OC') on its own, or does the conflict need the
                // profile of the tasks outside the window?
                auto uses_profile = energy <= supply;

                // The (i, t) pairs whose compulsory load the proof
                // pins: exactly what outside_profile counted.
                vector<pair<size_t, Integer>> pins;
                if (uses_profile) {
                    vector<bool> inside(starts.size(), false);
                    for (auto i : inside_tasks)
                        inside[i] = true;
                    for (auto j : active_tasks) {
                        // Exactly the tasks profile_within counted: mand_load
                        // holds only those known present. Pinning any other
                        // would claim load the arithmetic never used --- which
                        // VeriPB would *accept*, since by this point the reason
                        // context is contradictory and every RUP under it is
                        // vacuously valid, so nothing downstream would notice.
                        // That is exactly why it is written down here rather
                        // than left to a test to catch.
                        if (inside[j] || ! is_present(j))
                            continue;
                        auto lst = state.upper_bound(starts[j]);
                        auto eet = state.lower_bound(starts[j]) + llb(j);
                        for (Integer t = max(lst, a); t < min(eet, b); ++t)
                            pins.emplace_back(j, t);
                    }
                }

                auto justify = [&, a, b, inside_tasks, pins, uses_profile](const ReasonLiterals & reason) -> void {
                    if (! logger)
                        return;
                    logger->emit_proof_comment("cumulative overload conflict window=[" + std::to_string(a.raw_value) + "," +
                        std::to_string(b.raw_value) + ") rule=" + (uses_profile ? "ttoc" : "oc"));

                    // Tests only: each of these breaks one step of what
                    // follows, and each must make VeriPB reject the
                    // proof. See CumulativeProofMutation.
                    auto omit_capacity_line = std::holds_alternative<cumulative_proof_mutation::OmitCapacityLine>(mutation);
                    auto shrink_lemma_window = std::holds_alternative<cumulative_proof_mutation::ShrinkLemmaWindow>(mutation);
                    auto overstate_energy = std::holds_alternative<cumulative_proof_mutation::OverstateWindowEnergy>(mutation);

                    // The capacity available across the window, plus
                    // each contained task's window energy scaled by its
                    // height, plus (for (TTOC)) the pinned compulsory
                    // load of the tasks outside it. Each contained
                    // task's activity terms cancel exactly against its
                    // terms in the capacity lines, leaving a constraint
                    // with nothing but negative coefficients on the
                    // left and a positive right hand side.
                    PolBuilder pol;
                    for (Integer t = a; t < b; ++t) {
                        if (omit_capacity_line && t == b - 1_i)
                            continue;
                        auto line = capacity_lines.find(t);
                        if (line != capacity_lines.end())
                            pol.add(line->second);
                    }

                    for (auto i : inside_tasks) {
                        auto energy_line = window_energy::derive_window_energy(
                            *logger, reason, lemma_task(i), a, shrink_lemma_window ? b - 1_i : b, state.bounds(starts[i]), ProofLevel::Temporary);
                        if (! energy_line) {
                            // Only reachable under the shrunk-window
                            // mutation, where a task can be left with
                            // nothing derivable at all.
                            if (shrink_lemma_window)
                                continue;
                            throw ProofError{"cumulative overload: a task in the window has no derivable energy"};
                        }
                        if (! shrink_lemma_window && energy_line->bound != llb(i))
                            throw ProofError{"cumulative overload: window energy derivation is weaker than the check assumed"};

                        auto line = energy_line->line;
                        if (overstate_energy && i == inside_tasks.front()) {
                            WPBSum activity;
                            for (Integer t = energy_line->lo; t < energy_line->hi; ++t)
                                activity += 1_i * active_flags[i][static_cast<size_t>((t - per_task_t_lo[i]).raw_value)];
                            line =
                                logger->emit_rup_proof_line_under_reason(reason, move(activity) >= energy_line->bound + 1_i, ProofLevel::Temporary);
                        }
                        pol.add(line, hlb(i));
                    }

                    for (const auto & [j, t] : pins) {
                        auto [line, coeff] = pin_contributor(reason, j, t);
                        pol.add(line, coeff);
                    }

                    pol.emit(*logger, ProofLevel::Temporary);
                };

                inference.contradiction(logger, JustifyExplicitly{justify, ThenRUP::Yes, hints::CumulativeOverload{owner}}, reason_with_presence());
                return PropagatorState::DisableUntilBacktrack;
            }
        }
    }

    // The remaining work --- pushing each task's bounds away from the
    // times where placing it would overflow the profile --- is
    // time-table reasoning too.
    if (! rules.time_table)
        return PropagatorState::Enable;

    // One step of a bound-push proof chain: a blocked time t and the
    // tasks (≠ j) whose mandatory parts cover t. Used by both
    // lb-push and ub-push.
    struct ChainStep
    {
        Integer t;
        vector<size_t> contributing;
        // Start lower bound that, with lb(l_j), forces after_{j,t}=1:
        // the running bound for lb-push, t−lb(l_j)+1 for ub-push.
        Integer s_lo_after;
    };

    // Helper: emit (a)–(d) for one chain step.
    //
    // `ext` holds the literals added to the reason in PB form (= the
    // negation of "task j is active at t"-as-bounded-by-the-running
    // half):
    //   lb-push:  ext = {s_j ≥ t + 1}
    //   ub-push:  ext = {s_j ≤ t − l_j}
    //   falsify:  ext = {s_j ≥ t + 1, present_j = 0}, and just
    //             {present_j = 0} on the final step
    //
    // `emit_intermediate` deposits the ext disjunction as a unit clause under
    // reason — needed for every step except the last (the framework's wrapping
    // RUP closes the final inference).
    auto emit_chain_step = [&](size_t j_idx, Integer t, const vector<size_t> & contributing, const ExtLits & ext, Integer s_lo_after,
                               bool emit_intermediate, const ReasonLiterals & reason) -> void {
        // (a) Pin each task i ≠ j mandatory at t under the reason, and
        // (b) pin the pushed task j under the EXTENDED reason. Then
        // (c) combine all pinned load lines with C_t in one pol. After
        // cancellation the pol is dominated by (load − capacity)·Σext,
        // forcing the ext disjunction under the reason context.
        PolBuilder pol;
        pol.add(capacity_lines.at(t));
        for (auto i : contributing) {
            auto [line, coeff] = pin_contributor(reason, i, t);
            pol.add(line, coeff);
        }
        auto [j_line, j_coeff] = pin_pushed(reason, j_idx, t, ext, s_lo_after);
        pol.add(j_line, j_coeff);
        pol.emit(*logger, ProofLevel::Temporary);

        // (d) Deposit the running-bound advance as a fact under
        // reason for the next chain step's UP.
        if (emit_intermediate)
            logger->emit_rup_proof_line_under_reason(reason, plus_ext(WPBSum{}, ext, 1_i) >= 1_i, ProofLevel::Temporary);
    };

    for (auto j : active_tasks) {
        if (is_absent(j))
            continue;
        auto [cur_lb, cur_ub] = state.bounds(starts[j]);
        // A fixed start leaves nothing to push, but an undecided task with a
        // fixed start can still be shown to have nowhere to go.
        if (cur_lb == cur_ub && is_present(j))
            continue;

        auto lst_j = cur_ub, eet_j = cur_lb + llb(j);
        // Only a task known present put anything into the profile, so only that
        // one has something to discount before asking where it could go. An
        // undecided task's own load is not in mand_load and must not be
        // subtracted out of it.
        auto own_load_at = [&](Integer t) { return is_present(j) && lst_j < eet_j && t >= lst_j && t < eet_j ? hlb(j) : 0_i; };

        auto fits_at = [&](Integer s) -> bool {
            for (Integer t = s; t < s + llb(j); ++t)
                if (mand_load[(t - t_lo).raw_value] - own_load_at(t) + hlb(j) > capacity)
                    return false;
            return true;
        };

        auto is_blocked_at = [&](Integer t) -> bool { return mand_load[(t - t_lo).raw_value] - own_load_at(t) + hlb(j) > capacity; };

        auto contributors_at = [&](Integer t) -> vector<size_t> {
            vector<size_t> result;
            for (auto i : active_tasks) {
                if (i == j || ! is_present(i))
                    continue;
                auto lst_i = state.upper_bound(starts[i]);
                auto eet_i = state.lower_bound(starts[i]) + llb(i);
                if (lst_i < eet_i && t >= lst_i && t < eet_i)
                    result.push_back(i);
            }
            return result;
        };

        // The lb-push scan, which the presence falsification also reads: find
        // the smallest s in [cur_lb, cur_ub] with fits_at(s). If there is none,
        // no placement at all is left for this task.
        auto new_lb = cur_lb;
        while (new_lb <= cur_ub && ! fits_at(new_lb))
            ++new_lb;

        // Build the chain of blocked times carrying the running bound from
        // cur_lb up to `target`, picking the LARGEST blocked t in each step's
        // window so the bound advances as far as possible per step. Every
        // step's window contains a blocked time by construction (its running
        // bound does not fit), so the chain always reaches `target`.
        auto build_lb_chain = [&](Integer target) -> vector<ChainStep> {
            vector<ChainStep> chain;
            Integer running_bound = cur_lb;
            while (running_bound < target) {
                bool found = false;
                for (Integer t = running_bound + llb(j) - 1_i; t >= running_bound; --t)
                    if (is_blocked_at(t)) {
                        chain.push_back(ChainStep{t, contributors_at(t), running_bound});
                        running_bound = t + 1_i;
                        found = true;
                        break;
                    }
                if (! found)
                    break;
            }
            return chain;
        };

        if (! is_present(j)) {
            // Presence falsification. The task is undecided and, if it were
            // present, has nowhere left to start: new_lb ran off the end of its
            // domain. Replay the lb-push chain over the whole domain with "task
            // j is absent" carried as an extra disjunct on every line, so each
            // step says "either j starts later than this, or j is not here at
            // all". The last step's blocked time is at or beyond cur_ub --- that
            // is what makes it the last --- so there the start-side disjunct is
            // dropped: j's own upper bound in the reason already puts it before
            // that time, and asking for an order literal above the domain would
            // be asking for one that need not exist.
            //
            // The ClaimOneTooFar mutation fires where exactly one placement is
            // still open, so the conclusion is wrong rather than the route to
            // it. The chain then stops short --- its last window has no blocked
            // time --- and the wrapping RUP has nothing to close on, which is
            // what VeriPB must catch.
            if (new_lb <= cur_ub && ! (std::holds_alternative<cumulative_presence_mutation::ClaimOneTooFar>(presence_mutation) && new_lb == cur_ub))
                continue;
            auto chain = build_lb_chain(cur_ub + 1_i);
            if (chain.empty())
                continue;

            auto justify = [&, j, chain](const ReasonLiterals & reason) -> void {
                if (! logger)
                    return;
                // The marker a test counts to show the rule fired, and counts to
                // zero on the twin instance where it must not.
                logger->emit_proof_comment("cumulative optional: task " + std::to_string(j) + " cannot be placed anywhere, so it is absent");

                auto steps = std::holds_alternative<cumulative_presence_mutation::EmitNothing>(presence_mutation) ? 0 : chain.size();
                // Which task's absence the chain argues about: the one being
                // falsified, unless the WrongTask mutation points it at some
                // other optional task.
                auto about = j;
                if (std::holds_alternative<cumulative_presence_mutation::WrongTask>(presence_mutation))
                    for (auto k : active_tasks)
                        if (k != j && presence[k]) {
                            about = k;
                            break;
                        }

                for (size_t step = 0; step < steps; ++step) {
                    auto last = step + 1 == steps;
                    ExtLits ext;
                    if (! last)
                        ext.push_back(starts[j] > chain[step].t);
                    ext.push_back(*presence[about] == 0_i);
                    emit_chain_step(j, chain[step].t, chain[step].contributing, ext, chain[step].s_lo_after, ! last, reason);
                }
            };

            inference.infer_equal(
                logger, *presence[j], 0_i, JustifyExplicitly{justify, ThenRUP::Yes, hints::Cumulative{owner}}, reason_with_presence());
            continue;
        }

        // lb-push: chain through blocked t's up to the first placement that fits.
        if (new_lb > cur_lb) {
            auto chain = build_lb_chain(new_lb);

            auto justify = [&, j, chain](const ReasonLiterals & reason) -> void {
                if (! logger)
                    return;
                for (size_t step = 0; step < chain.size(); ++step)
                    emit_chain_step(j, chain[step].t, chain[step].contributing, ExtLits{starts[j] > chain[step].t}, chain[step].s_lo_after,
                        step + 1 < chain.size(), reason);
            };

            inference.infer_greater_than_or_equal(
                logger, starts[j], new_lb, JustifyExplicitly{justify, ThenRUP::Yes, hints::Cumulative{owner}}, reason_with_presence());
        }

        // ub-push: mirror image. Pick SMALLEST blocked t in each
        // step's window so the upper bound drops the most. Each
        // step turns a blocked t into the fact s_j ≤ t − l_j.
        auto new_ub = cur_ub;
        while (new_ub >= cur_lb && ! fits_at(new_ub))
            --new_ub;
        if (new_ub < cur_ub) {
            vector<ChainStep> chain;
            Integer running_bound = cur_ub;
            while (running_bound > new_ub) {
                bool found = false;
                for (Integer t = running_bound; t <= running_bound + llb(j) - 1_i; ++t)
                    if (is_blocked_at(t)) {
                        chain.push_back(ChainStep{t, contributors_at(t), t - llb(j) + 1_i});
                        running_bound = t - llb(j);
                        found = true;
                        break;
                    }
                if (! found)
                    break;
            }

            auto justify = [&, j, chain](const ReasonLiterals & reason) -> void {
                if (! logger)
                    return;
                for (size_t step = 0; step < chain.size(); ++step)
                    emit_chain_step(j, chain[step].t, chain[step].contributing, ExtLits{starts[j] < chain[step].t - llb(j) + 1_i},
                        chain[step].s_lo_after, step + 1 < chain.size(), reason);
            };

            inference.infer_less_than(
                logger, starts[j], new_ub + 1_i, JustifyExplicitly{justify, ThenRUP::Yes, hints::Cumulative{owner}}, reason_with_presence());
        }
    }

    return PropagatorState::Enable;
}

auto Cumulative::starts() const -> const vector<IntegerVariableID> &
{
    return _starts;
}

auto Cumulative::lengths() const -> const vector<IntegerVariableID> &
{
    return _lengths;
}

auto Cumulative::heights() const -> const vector<IntegerVariableID> &
{
    return _heights;
}

auto Cumulative::presences() const -> const vector<IntegerVariableID> &
{
    return _presences;
}

auto Cumulative::capacity() const -> IntegerVariableID
{
    return _capacity;
}

auto ConstraintProofModelData<Cumulative>::primary_row_role(const Cumulative &) -> std::optional<string>
{
    return std::nullopt;
}

auto ConstraintProofModelData<Cumulative>::capacity_row_role(Integer t) -> string
{
    // Must stay the string define_proof_model labels the row with.
    return "cap_" + std::to_string(t.raw_value);
}

auto ConstraintProofModelData<Cumulative>::before_flag_key(size_t task, Integer t) -> ProofFlagKey
{
    return ProofFlagKey{{static_cast<long long>(task), t.raw_value}, "cb"};
}

auto ConstraintProofModelData<Cumulative>::after_flag_key(size_t task, Integer t) -> ProofFlagKey
{
    return ProofFlagKey{{static_cast<long long>(task), t.raw_value}, "ca"};
}

auto ConstraintProofModelData<Cumulative>::active_flag_key(size_t task, Integer t) -> ProofFlagKey
{
    return ProofFlagKey{{static_cast<long long>(task), t.raw_value}, "cact"};
}

auto ConstraintProofModelData<Cumulative>::contribution_flag_key(size_t task, Integer t, Integer bit) -> ProofFlagKey
{
    return ProofFlagKey{{static_cast<long long>(task), t.raw_value, bit.raw_value}, "cc"};
}

auto ConstraintProofModelData<Cumulative>::contribution_ge_row_role(size_t task, Integer t) -> string
{
    // cake_pb_cp's own name for this row. Must stay the string
    // define_proof_model labels it with, and must stay cake's.
    return std::to_string(task) + "_" + std::to_string(t.raw_value) + "_cge";
}

auto ConstraintProofModelData<Cumulative>::contribution_le_row_role(size_t task, Integer t) -> string
{
    return std::to_string(task) + "_" + std::to_string(t.raw_value) + "_cle";
}

auto ConstraintProofModelData<Cumulative>::contribution_zero_row_role(size_t task, Integer t) -> string
{
    return std::to_string(task) + "_" + std::to_string(t.raw_value) + "_cz";
}

auto ConstraintProofModelData<Cumulative>::end_lower_bound_role(size_t task) -> string
{
    // Must stay the string install_propagators' initialiser publishes under.
    return "end_ge_" + std::to_string(task);
}

auto Cumulative::constraint_type() const -> std::string
{
    // The optional form is a different constraint, not a variant of this one:
    // its active flags carry a third conjunct, so a verified encoder for
    // "cumulative" would re-derive a strictly different --- and weaker --- set
    // of capacity rows from the same s-expression. cake_pb_cp has no optional
    // cumulative encoder today, so naming it apart is what keeps the
    // verified-encoding chain honest about the gap rather than silently
    // mismatching.
    return _presences.empty() ? "cumulative" : "cumulative_optional";
}

auto Cumulative::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    vector<SExpr> starts, lengths, heights, presences;
    for (const auto & v : _starts)
        starts.push_back(tracker.s_expr_term_of(v));
    for (const auto & l : _lengths)
        lengths.push_back(tracker.s_expr_term_of(l));
    for (const auto & h : _heights)
        heights.push_back(tracker.s_expr_term_of(h));
    for (const auto & p : _presences)
        presences.push_back(tracker.s_expr_term_of(p));
    vector<SExpr> terms{SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(std::move(starts)),
        SExpr::list(std::move(lengths)), SExpr::list(std::move(heights))};
    // The presences list sits where the FlatZinc builtin puts it, between the
    // heights and the capacity, and is absent entirely for the non-optional
    // form so that its s-expression is unchanged.
    if (! _presences.empty())
        terms.push_back(SExpr::list(std::move(presences)));
    terms.push_back(tracker.s_expr_term_of(_capacity));
    return SExpr::list(std::move(terms));
}

template auto gcs::innards::propagate_cumulative(const CumulativeInputs &, const State &, SimpleInferenceTracker &, ProofLogger * const)
    -> PropagatorState;

template auto gcs::innards::propagate_cumulative(const CumulativeInputs &, const State &, EagerProofLoggingInferenceTracker &, ProofLogger * const)
    -> PropagatorState;
