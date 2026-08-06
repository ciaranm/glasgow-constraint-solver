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
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <algorithm>
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
using std::unique_ptr;
using std::vector;
using std::ranges::sort;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

namespace
{
    auto const_value_of(const IntegerVariableID & v) -> Integer
    {
        return std::get<ConstantIntegerVariableID>(v).const_value;
    }

    auto as_constant_var_ids(const vector<Integer> & vals) -> vector<IntegerVariableID>
    {
        vector<IntegerVariableID> result;
        result.reserve(vals.size());
        for (const auto & v : vals)
            result.push_back(constant_variable(v));
        return result;
    }

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
    if (is_constant_variable(_capacity) && const_value_of(_capacity) < 0_i)
        throw InvalidProblemDefinitionException{"Cumulative: capacity must be non-negative"};
    for (const auto & l : _lengths)
        if (is_constant_variable(l) && const_value_of(l) < 0_i)
            throw InvalidProblemDefinitionException{"Cumulative: lengths must be non-negative"};
    for (const auto & h : _heights)
        if (is_constant_variable(h) && const_value_of(h) < 0_i)
            throw InvalidProblemDefinitionException{"Cumulative: heights must be non-negative"};
}

Cumulative::Cumulative(vector<IntegerVariableID> starts, vector<Integer> lengths, vector<Integer> heights, Integer capacity) :
    Cumulative(move(starts), as_constant_var_ids(lengths), as_constant_var_ids(heights), constant_variable(capacity))
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
        if (is_constant_variable(p) && const_value_of(p) != 0_i && const_value_of(p) != 1_i)
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

auto gcs::innards::cumulative_task_presence(const optional<IntegerVariableID> & posted) -> CumulativeTaskPresence
{
    if (! posted)
        return CumulativeTaskPresence{};

    if (! is_constant_variable(*posted))
        return CumulativeTaskPresence{*posted, false};

    auto value = const_value_of(*posted);
    if (value == 1_i)
        return CumulativeTaskPresence{};
    if (value == 0_i)
        return CumulativeTaskPresence{*posted, true};
    throw InvalidProblemDefinitionException{"Cumulative: presences must be within {0, 1}"};
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
    // cumulative_task_presence is shared rather than open-coded here.
    _presence.assign(n, std::nullopt);
    vector<bool> never_present(n, false);
    for (size_t i = 0; i < n; ++i) {
        auto resolved = cumulative_task_presence(_presences.empty() ? std::nullopt : make_optional(_presences[i]));
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
        _length_vals.push_back(is_constant_variable(l) ? const_value_of(l) : 0_i);
        _length_lb.push_back(initial_state.lower_bound(l));
        _length_ub.push_back(initial_state.upper_bound(l));
    }
    for (const auto & h : _heights) {
        _height_vals.push_back(is_constant_variable(h) ? const_value_of(h) : 0_i);
        _height_ub.push_back(initial_state.upper_bound(h));
    }
    if (is_constant_variable(_capacity))
        _capacity_val = const_value_of(_capacity);

    // Tasks whose length can only ever be 0, or whose height can only ever be 0,
    // or which are constantly absent, never raise the load profile.
    _active_tasks.reserve(n);
    for (size_t i = 0; i < n; ++i)
        if (_length_ub[i] > 0_i && _height_ub[i] > 0_i && ! never_present[i])
            _active_tasks.push_back(i);

    if (_active_tasks.empty())
        return false;

    // The possible-active window of task i is [lb(s_i), ub(s_i)+ub(l_i)-1]; the
    // per-(i,t) flags span it, so it must use the largest possible duration.
    _per_task_t_lo.assign(n, 0_i);
    _per_task_t_hi.assign(n, 0_i);
    for (auto i : _active_tasks) {
        auto [s_lo, s_hi] = initial_state.bounds(_starts[i]);
        _per_task_t_lo[i] = s_lo;
        _per_task_t_hi[i] = s_hi + _length_ub[i] - 1_i;
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

auto gcs::innards::prepare_cumulative_overload_check(const vector<IntegerVariableID> & starts, const vector<IntegerVariableID> & lengths,
    const vector<IntegerVariableID> & heights, const vector<size_t> & active_tasks, const vector<Integer> & per_task_t_lo,
    const vector<Integer> & per_task_t_hi, const State & initial_state) -> CumulativeOverloadData
{
    CumulativeOverloadData result;
    // Which tasks the window-energy lemma can speak about: a constant length
    // and height (so the task's energy is a constant, and its load in C_t is
    // h·active rather than the bit-linearised contrib), and a start that is a
    // plain variable with an order encoding, since the lemma bridges the
    // before/after flags to the start's order literals. A task that is not
    // eligible is not lost to the check: whatever it must occupy still counts,
    // through the profile term of the (TTOC) strengthening.
    //
    // Seam for optional tasks (#543): once a task can be absent, only one
    // whose presence is fixed true may join the energy set or the profile, and
    // its presence literal joins the reason. Nothing here consults a presence
    // variable yet because there is not one to consult.
    result.overload_tasks.clear();
    for (auto i : active_tasks) {
        if (! is_constant_variable(lengths[i]) || ! is_constant_variable(heights[i]))
            continue;
        if (const_value_of(lengths[i]) <= 0_i || const_value_of(heights[i]) <= 0_i)
            continue;
        if (! std::holds_alternative<SimpleIntegerVariableID>(starts[i]))
            continue;
        // A start whose domain is exactly {0, 1} is direct-only encoded, so it
        // has no order literals for the lemma's bridges to cancel against.
        auto [s_lo, s_hi] = initial_state.bounds(starts[i]);
        if (s_lo == 0_i && s_hi == 1_i)
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
                auto contrib = contrib_sum_of(cc);
                model.add_constraint(contrib + -1_i * _heights[i] >= 0_i, HalfReifyOnConjunctionOf{active});
                model.add_constraint(contrib + -1_i * _heights[i] <= 0_i, HalfReifyOnConjunctionOf{active});
                model.add_constraint(contrib <= 0_i, HalfReifyOnConjunctionOf{! active});
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

    // Per variable-duration task, the in-proof end = s + l definition lines
    // {end_ge, end_le}, filled by the initialiser and read by the propagator's
    // materialise_after_sum. Shared so the cache survives across propagator calls.
    auto end_lines = make_shared<vector<std::optional<std::pair<ProofLine, ProofLine>>>>(_starts.size());

    propagators.install_initialiser([starts = _starts, lengths = _lengths, ends = _end, active_tasks = _active_tasks, after_flags = _after_flags,
                                        end_lines](State &, auto &, ProofLogger * const logger) -> void {
        if (! logger || logger->get_assertion_level() > AssertionLevel::Off)
            return;
        auto & tracker = logger->names_and_ids_tracker();
        // Bit-define each variable-duration end = s + l as a conservative
        // extension FIRST (introduce_bits_of needs end's bits fresh for its
        // witnesses), caching end's {end_ge, end_le}. cake has no end variable,
        // so this lives entirely in the proof --- nothing in the OPB to match.
        for (auto i : active_tasks)
            if (ends[i].has_value())
                (*end_lines)[i] = logger->introduce_bits_of(WPBSum{} + 1_i * starts[i] + 1_i * lengths[i], *ends[i], ProofLevel::Top);
        // Then, per (i, t), emit the bridge lemma `end ≥ t+1 → after`:
        //   pol( @v[id][i_t][ca][f] : ¬after → s+l ≤ t )  +  ( end ≤ s+l )
        //   = ( M·after − end + t ≥ 0 ).
        // The s+l bits cancel exactly, leaving a single-variable-in-end handle
        // that makes the propagator's after pin RUP-closable even though after
        // is reified on the two-variable s+l. end_le is the cancelling term.
        for (auto i : active_tasks) {
            if (! ends[i].has_value())
                continue;
            auto end_le = (*end_lines)[i]->second;
            for (const auto & after : after_flags[i]) {
                PolBuilder lemma;
                lemma.add(ProofLineLabel{tracker.name_of(after) + "[f]"});
                lemma.add(end_le);
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
        .ends = move(_end),
        .end_lines = end_lines,
        .capacity_lines = move(_capacity_lines),
        .rules = _rules,
        .proof_mutation = _proof_mutation,
        .presence_mutation = _presence_mutation,
        .overload_tasks = move(_overload_tasks),
        .time_slot_prefix = move(_time_slot_prefix),
        .time_slot_lo = _time_slot_lo};

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
    const auto & end_lines = inputs.end_lines;
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
        sp.add((*end_lines)[i]->first);
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
            auto [s_lo, s_hi] = state.bounds(starts[i]);
            auto p = llb(i), h = hlb(i);
            candidates.push_back(Candidate{i, s_lo, s_hi + p, p * h, h * max(0_i, s_lo + p - s_hi)});
        }
        // An empty candidate list leaves window_starts empty too, so the window
        // loop below simply does not run; no early exit needed.
        sort(candidates, [](const Candidate & a, const Candidate & b) { return a.lct < b.lct; });

        vector<Integer> window_starts;
        window_starts.reserve(candidates.size());
        for (const auto & c : candidates)
            window_starts.push_back(c.est);
        sort(window_starts);

        for (size_t w = 0; w < window_starts.size(); ++w) {
            if (w > 0 && window_starts[w] == window_starts[w - 1])
                continue;
            auto a = window_starts[w];

            Integer energy = 0_i, inside_mandatory = 0_i;
            vector<size_t> inside_tasks;
            for (const auto & c : candidates) {
                if (c.est < a)
                    continue;
                energy += c.energy;
                inside_mandatory += c.mandatory;
                inside_tasks.push_back(c.task);

                auto b = c.lct;
                auto supply = capacity * slots_within(a, b);
                auto outside_profile = rules.profile_overload ? profile_within(a, b) - inside_mandatory : 0_i;
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
                        auto energy_line = window_energy::derive_window_energy(*logger, reason,
                            window_energy::ConstantLengthTask{std::get<SimpleIntegerVariableID>(starts[i]), llb(i), per_task_t_lo[i], before_flags[i],
                                after_flags[i], active_flags[i]},
                            a, shrink_lemma_window ? b - 1_i : b, state.bounds(starts[i]), ProofLevel::Temporary);
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
