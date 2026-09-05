#include <gcs/constraints/cumulative/checkpoint_recovery.hh>
#include <gcs/constraints/cumulative/cumulative.hh>
#include <gcs/constraints/cumulative/hints.hh>
#include <gcs/constraints/cumulative/propagate.hh>
#include <gcs/constraints/innards/guaranteed_contribution.hh>
#include <gcs/constraints/innards/window_energy.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/power.hh>
#include <gcs/innards/proofs/bits_encoding.hh>
#include <gcs/innards/proofs/flag_bridge.hh>
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
#include <cstdlib>
#include <memory>
#include <optional>
#include <ranges>
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
using std::nullopt;
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
    // The encoding a Cumulative writes when with_encoding() was not called.
    // The environment rather than a constructor argument because what it is
    // for is running an existing fixture set --- which builds its Cumulatives
    // in sixty places --- under the other arm without touching any of them.
    //
    // An unrecognised spelling throws, where GCS_ASSERTION_LEVEL's reader
    // warns and carries on. The difference is what a mistake costs: a mistyped
    // assertion level writes a proof at the wrong level, which shows up; a
    // mistyped encoding silently runs the arm that was already covered, and
    // the run goes green having checked nothing new.
    auto default_cumulative_encoding() -> CumulativeEncoding
    {
        static const auto value = [] {
            const auto * const env = std::getenv("GCS_CUMULATIVE_ENCODING");
            if (! env || ! *env)
                return CumulativeEncoding::TimeIndexed;
            string spelling{env};
            if (spelling == "time-indexed")
                return CumulativeEncoding::TimeIndexed;
            else if (spelling == "both")
                return CumulativeEncoding::Both;
            else if (spelling == "both-recovering")
                return CumulativeEncoding::BothRecovering;
            else if (spelling == "start-checkpoint")
                return CumulativeEncoding::StartCheckpoint;
            throw UnexpectedException{"unrecognised GCS_CUMULATIVE_ENCODING value '" + spelling + "'"};
        }();
        return value;
    }

    // The variable-height contribution h_i·active is linearised over cake's
    // per-bit contribution flags cc_k (weight 2^k): contrib = Σ 2^k · cc_k.
    // What the three per-(task, time) flags say. One statement each, because
    // #780 defines them two ways --- as labelled OPB rows under the
    // time-indexed encodings, and as `red` steps inside the proof under the
    // start-checkpoint one --- and a second copy that drifted would make a flag
    // mean one thing to the encoder and another to everything that cites it.
    //
    // `operator>=` renders as a WPBSumLE like `operator<=` does, so all three
    // come back in the one type the reifying calls take.
    auto per_time_before_says(const IntegerVariableID & start, Integer t) -> WPBSumLE
    {
        return WPBSum{} + 1_i * start <= t;
    }

    // after_{i,t} <-> task i not yet finished at t <-> s_i + l_i >= t + 1.
    // Constant length: single-variable s_i >= t-l+1. Variable length: reify on
    // s_i + l_i directly (any constant operand folds in), which matches
    // cake_pb_cp's after <-> s + l >= t+1. The proof-only end (when both vary)
    // is NOT used here; it is only the single-variable handle the propagator
    // pins through, bridged to this flag by the lemma the initialiser emits.
    auto per_time_after_says(const IntegerVariableID & start, const IntegerVariableID & length, Integer t) -> WPBSumLE
    {
        if (is_constant_variable(length))
            return WPBSum{} + 1_i * start >= t - constant_value_of(length) + 1_i;
        return WPBSum{} + 1_i * start + 1_i * length >= t + 1_i;
    }

    // active_{i,t} <-> before /\ after, plus the presence conjunct for an
    // optional task. The presence literal is the {0,1} variable's single PB
    // atom, so the three-way AND costs one more term in the same two
    // reification halves --- no extra flag, and nothing else in the encoding
    // has to know whether the task is optional. An absent task fails the AND at
    // every t, so it drops out of every capacity row, which is exactly "an
    // absent task consumes nothing".
    auto per_time_active_says(const ProofFlag & before, const ProofFlag & after, const optional<IntegerVariableID> & presence) -> WPBSumLE
    {
        auto conjuncts = WPBSum{} + 1_i * before + 1_i * after;
        auto arity = 2_i;
        if (presence) {
            conjuncts += 1_i * (*presence == 1_i);
            arity = 3_i;
        }
        return move(conjuncts) >= arity;
    }

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

auto Cumulative::with_encoding(CumulativeEncoding encoding) -> Cumulative &
{
    _encoding = encoding;
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
    if (_encoding)
        result->with_encoding(*_encoding);
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
    _height_lb.clear();
    _height_ub.clear();
    _length_vals.reserve(n);
    _length_lb.reserve(n);
    _length_ub.reserve(n);
    _height_vals.reserve(n);
    _height_lb.reserve(n);
    _height_ub.reserve(n);
    for (const auto & l : _lengths) {
        _length_vals.push_back(is_constant_variable(l) ? constant_value_of(l) : 0_i);
        _length_lb.push_back(initial_state.lower_bound(l));
        _length_ub.push_back(initial_state.upper_bound(l));
    }
    for (const auto & h : _heights) {
        _height_vals.push_back(is_constant_variable(h) ? constant_value_of(h) : 0_i);
        // The lower bound is the *declared* one, which is what decides whether
        // the variable's bit encoding carries a sign bit --- and so whether
        // bit k of it has weight 2^k, which #780 step 10 needs when it defines
        // a contribution bit as a conjunction with one. Heights are
        // non-negative by the time prepare is done, but a declared bound below
        // zero would still shift every weight.
        _height_lb.push_back(initial_state.lower_bound(h));
        _height_ub.push_back(initial_state.upper_bound(h));
    }
    if (is_constant_variable(_capacity))
        _capacity_val = constant_value_of(_capacity);

    // #780: can every height's own bits be cited? A constant needs none; a
    // plain variable with a declared lower bound of zero or more has bit k at
    // weight 2^k; a view has no bits of its own, and a declared bound below
    // zero puts a sign bit in and shifts every weight. Where the answer is no,
    // a variable height's contribution stays linearised by three rows per
    // pair, and the per-(task, time) family stays in the model --- see
    // define_proof_model.
    _height_bits_citable = std::ranges::all_of(std::views::iota(std::size_t{0}, _heights.size()), [&](std::size_t i) {
        return is_constant_variable(_heights[i]) || (std::holds_alternative<SimpleIntegerVariableID>(_heights[i]) && _height_lb[i] >= 0_i);
    });

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
    // Which tasks the window-energy lemma can speak about: a start that is a
    // plain variable with an order encoding, since the lemma bridges the
    // before/after flags to the start's order literals. A task that is not
    // eligible is not lost to the check: whatever it must occupy still counts,
    // through the profile term of the (TTOC) strengthening.
    //
    // Neither a variable length nor a variable height is turned away any more
    // (#689). Both are counted at what the task *guarantees* rather than at
    // what it might use, and both are plain variables for the same reason the
    // start is --- what the derivations need is an order literal to cancel
    // against.
    //
    // A variable **length** is counted over [start, start + lb(length)), which
    // the execution interval contains, by bridging the `after` flags back onto
    // the start's order literals through the length's own.
    //
    // A variable **height** does not change what the lemma derives at all: it
    // changes what a capacity row carries, which is the bit-linearised
    // `contrib` rather than `h·active`, so a citer converts the activity into
    // contribution terms with guaranteed_contribution_row before the two can
    // cancel. That conversion is #686's, and it is what a *derived*
    // Cumulative's tasks have already been through by the time they reach here
    // --- which is how an all-variable-height donor's energy got counted at all
    // while a posted one's did not.
    //
    // What is asked here of either is only that it can be positive: a task
    // whose length or height can only be zero is not an active task in the
    // first place. Whether the bound it reaches is worth anything is asked at
    // every node, in the candidate sweep, and not here.
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
        if (! std::holds_alternative<SimpleIntegerVariableID>(starts[i]) || direct_only_encoded(starts[i]))
            continue;
        if (is_constant_variable(lengths[i])) {
            if (constant_value_of(lengths[i]) <= 0_i)
                continue;
        }
        else if (! std::holds_alternative<SimpleIntegerVariableID>(lengths[i]) || initial_state.upper_bound(lengths[i]) <= 0_i ||
            direct_only_encoded(lengths[i]))
            continue;
        if (is_constant_variable(heights[i])) {
            if (constant_value_of(heights[i]) <= 0_i)
                continue;
        }
        // A {0,1} height is not excluded, unlike a {0,1} start or length: the
        // conversion resolves its atom to a bare literal rather than to a
        // defining line, which costs it its hints and nothing else.
        else if (! std::holds_alternative<SimpleIntegerVariableID>(heights[i]) || initial_state.upper_bound(heights[i]) <= 0_i)
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
    // #780 step 10. The per-(task, time) flags move out of the OPB and into the
    // proof under StartCheckpoint, which is where they stop being needed as
    // model objects: the per-time capacity rows are what mention them, and that
    // is the block this encoding does without.
    //
    // A variable height's contribution bits come too. Out of the model they
    // stop needing three rows at all: the product h_i * cact_{i,t} linearises
    // bit by bit into a *conjunction*,
    //
    //     cc_{i,t,k}  <->  cact_{i,t}  /\  bit_k(h_i)
    //
    // which is one two-way reification of a fresh flag over literals that
    // already exist --- the same primitive the activity flag itself uses. The
    // three `cge` / `cle` / `cz` rows then fall out of those definitions rather
    // than being asserted; see the initialiser, and the recovery's swap, which
    // got shorter for it.
    //
    // It needs the height's own bits, which means a plain variable rather than
    // a view, and no sign bit --- so a declared lower bound of zero or more.
    // Heights are non-negative anyway (prepare checks), but a *declared* bound
    // below zero would still put a sign bit in the encoding and shift every
    // weight, so this asks rather than assumes. A constraint with a height it
    // cannot ask about keeps the whole family in the model: the contribution
    // rows are half-reified on the activity flag, so a mixture is not available.
    _per_time_flags_in_proof = _encoding.value_or(default_cumulative_encoding()) == CumulativeEncoding::StartCheckpoint && _height_bits_citable;

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
            // Named either way; *defined* here only where the definition is an
            // OPB row. Under _per_time_flags_in_proof the two halves are
            // emitted as `red` steps by the install initialiser instead, which
            // is the whole of #780's step 10: these three rows per (task, time)
            // are 99.9% of the OPB on the instances the encoding exists for.
            auto mint = [&](const char * annotation, const WPBSumLE & says) {
                if (_per_time_flags_in_proof)
                    return model.names_and_ids_tracker().create_proof_flag_values(_constraint_id, it, annotation);
                return model.create_proof_flag_values_fully_reifying(_constraint_id, it, annotation, says);
            };
            auto before = mint("cb", per_time_before_says(_starts[i], t));
            auto after = mint("ca", per_time_after_says(_starts[i], _lengths[i], t));
            auto active = mint("cact", per_time_active_says(before, after, _presence[i]));
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
                if (! _per_time_flags_in_proof) {
                    auto contrib = contrib_sum_of(cc);
                    model.add_labelled_constraint(_constraint_id, ConstraintProofModelData<Cumulative>::contribution_ge_row_role(i, t),
                        contrib + -1_i * _heights[i] >= 0_i, HalfReifyOnConjunctionOf{active});
                    model.add_labelled_constraint(_constraint_id, ConstraintProofModelData<Cumulative>::contribution_le_row_role(i, t),
                        contrib + -1_i * _heights[i] <= 0_i, HalfReifyOnConjunctionOf{active});
                    model.add_labelled_constraint(_constraint_id, ConstraintProofModelData<Cumulative>::contribution_zero_row_role(i, t),
                        contrib <= 0_i, HalfReifyOnConjunctionOf{! active});
                }
                _contrib_flags[i].push_back(move(cc));
            }
        }
    }

    // #780: under CumulativeEncoding::StartCheckpoint the per-time capacity
    // rows are not written at all, so that a rule which still reads
    // `capacity_lines` finds nothing and its certificate fails loudly rather
    // than quietly keeping a dependency on a block that is going away. Only
    // where the recovery can actually supply a replacement, though --- a
    // variable height or an optional task has no recovered row to fall back on,
    // and dropping the model's would leave the constraint with no capacity row
    // at all rather than merely an unconverted one.
    //
    // Note this gates the capacity *rows* only. The per-(task, time) flags
    // above stay: every rule's activity vocabulary is still stated over them,
    // and moving them to lazily-minted objects is its own step of #780.
    auto encoding = _encoding.value_or(default_cumulative_encoding());
    auto shape_supports_recovery = cumulative_shape_supports_checkpoint_recovery(_active_tasks, _presence, _lengths, _heights, _capacity);
    auto omit_per_time_capacity_rows = encoding == CumulativeEncoding::StartCheckpoint && shape_supports_recovery;

    for (Integer t = global_lo; t <= global_hi && ! omit_per_time_capacity_rows; ++t) {
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

    if (encoding == CumulativeEncoding::TimeIndexed)
        return;

    // #780: under CumulativeEncoding::StartCheckpoint a shape the recovery
    // cannot speak about has just kept its per-time block, above. Writing the
    // checkpoint block beside it as well would be pure growth: no rule can
    // cite it, because every citer goes through a recovery that declines this
    // shape before it looks at the model at all. So StartCheckpoint on a
    // declined shape *is* TimeIndexed, which is what "start-checkpoint
    // wherever the recovery reaches" has to mean once the default flips ---
    // otherwise every variable-length, variable-height, variable-capacity or
    // optional-task model would silently start paying for two encodings.
    //
    // Both and BothRecovering keep writing it for every shape. They are the
    // differential arms, and a checkpoint row over a shape the recovery
    // declines is still a row veripb checks against the solutions, which is
    // how the block was soundness-checked in the first place.
    if (encoding == CumulativeEncoding::StartCheckpoint && ! shape_supports_recovery)
        return;

    // Start-checkpoint encoding (issue #780), emitted *alongside* the
    // time-indexed block above rather than instead of it:
    //   for each ordered pair (i, j) of tasks that can raise the profile:
    //     sb_{i,j}   ⇔  starts[i] ≤ starts[j]
    //     sa_{i,j}   ⇔  starts[i] + lengths[i] ≥ starts[j] + 1
    //     sact_{i,j} ⇔  sb_{i,j} ∧ sa_{i,j} [ ∧ presences[i] = 1 ]
    //   for each such task j:
    //     Σ heights[i]·sact_{i,j} ≤ capacity
    //
    // It says the same thing the block above does, in O(n²) rows rather than
    // O(n × horizon): the load profile is a step function that only rises at
    // the start of a task which could occupy the resource, so a time point
    // over capacity is dominated by the last such start at or before it, and
    // checking every start checks every peak. Lengths, heights and the
    // capacity are all non-negative (the constructor and prepare check that),
    // so a checkpoint with nothing active is satisfied rather than merely
    // vacuous. A checkpoint at a task that turns out to be absent, or to have
    // length zero, is harmless --- its start is still *some* time point, and
    // the capacity holds at every time point --- it just does not count
    // towards sufficiency, which is why the checkpoints are over _active_tasks
    // and not over every task.
    //
    // Nothing cites these yet, and no propagator or rule knows they exist.
    // They are here to be checked against the family that *is* load-bearing
    // before anything is derived from them: a checkpoint row that says too
    // much is a solution VeriPB refuses on the `solx` line of any enumeration
    // test, which is a soundness check the per-time block cannot dodge for
    // them. What it does not check is sufficiency --- that these imply the
    // per-time rows --- and that only gets tested as inferences move over.
    // Deriving the per-time rows from these, and deleting the block above, is
    // the rest of #780.
    //
    // Not windowed, unlike the block above: every ordered pair gets flags,
    // including pairs that could never be active together. Whether pruning
    // those is worth the recovery having to know a pair may be missing is a
    // measurement, not something to guess at here.
    for (auto j : _active_tasks) {
        WPBSum load;
        // What the diagonal contributes when it needs no flag: a constant
        // height, taken unconditionally, which belongs on the right hand side
        // rather than as a term.
        Integer fixed_load = 0_i;
        for (auto i : _active_tasks) {
            std::vector<long long> ij{static_cast<long long>(i), static_cast<long long>(j)};
            std::optional<ProofFlag> active;

            if (i != j) {
                auto before =
                    model.create_proof_flag_values_fully_reifying(_constraint_id, ij, "sb", WPBSum{} + 1_i * _starts[i] + -1_i * _starts[j] <= 0_i);
                // after_{i,j} ⇔ task i has not finished by the time j starts ⇔
                // s_i + l_i ≥ s_j + 1. A constant length folds into the right
                // hand side, exactly as it does per (i, t); a variable one
                // stays on the left, which makes this a three-variable row.
                // That costs nothing here --- a PB row does not care how many
                // variables it names --- but it is why the per-(i,t) family
                // needed the proof-only `end` proxy, and a pin of this flag
                // will need the same treatment per pair rather than per time.
                auto after = is_constant_variable(_lengths[i]) ? model.create_proof_flag_values_fully_reifying(_constraint_id, ij, "sa",
                                                                     WPBSum{} + 1_i * _starts[i] + -1_i * _starts[j] >= 1_i - _length_vals[i])
                                                               : model.create_proof_flag_values_fully_reifying(_constraint_id, ij, "sa",
                                                                     WPBSum{} + 1_i * _starts[i] + 1_i * _lengths[i] + -1_i * _starts[j] >= 1_i);
                auto conjuncts = WPBSum{} + 1_i * before + 1_i * after;
                auto arity = 2_i;
                if (_presence[i]) {
                    conjuncts += 1_i * (*_presence[i] == 1_i);
                    arity = 3_i;
                }
                active = model.create_proof_flag_values_fully_reifying(_constraint_id, ij, "sact", move(conjuncts) >= arity);
            }
            else {
                // The diagonal: is j running at the moment j starts? before is
                // a tautology and after reduces to lengths[j] ≥ 1, so what is
                // left is that conjunct and the presence. Both matter: a task
                // that can have length zero, or that can be absent, must not
                // be charged for a resource it never takes, which is what
                // putting a bare h_j on the row would do.
                //
                // Where neither says anything --- a constant length, which is
                // at least 1 for an active task, and no presence --- the term
                // *is* unconditional, so it goes on the row as itself and no
                // flag is minted. That is what the nullopt from
                // pair_active_flag_key means on a diagonal.
                auto conjuncts = WPBSum{};
                auto arity = 0_i;
                if (! is_constant_variable(_lengths[j])) {
                    conjuncts += 1_i * _lengths[j];
                    arity += 1_i;
                }
                if (_presence[j]) {
                    // Scaled to the length's own arity so that one term cannot
                    // stand in for the other: with a variable length the row
                    // is lengths[j] + ub(lengths[j])·present ≥ 1 + ub, which
                    // needs both.
                    auto weight = (arity == 0_i) ? 1_i : _length_ub[j];
                    conjuncts += weight * (*_presence[j] == 1_i);
                    arity += weight;
                }
                if (arity > 0_i)
                    active = model.create_proof_flag_values_fully_reifying(_constraint_id, ij, "sact", move(conjuncts) >= arity);
            }

            if (! active) {
                // Unconditional: the height itself, constant or not.
                if (is_constant_variable(_heights[i]))
                    fixed_load += _height_vals[i];
                else
                    load += 1_i * _heights[i];
                continue;
            }

            if (is_constant_variable(_heights[i]))
                load += _height_vals[i] * *active;
            else {
                // A variable height's contribution is the product h_i·active,
                // linearised over per-bit flags exactly as the per-(i,t) block
                // does it; see there for what the three rows say.
                // Bit by bit, `contrib = h_i * sact_{i,j}` *is* a conjunction:
                // scc_{i,j,k} <-> sact_{i,j} /\ bit_k(h_i). Two reification
                // halves per bit, where the three-row linearisation this
                // replaced took `scge` / `scle` / `scz` per pair --- and, more
                // to the point, the halves are what let the recovery swap a
                // pair bit for a per-time one with a single rup per bit rather
                // than a case split. The per-time family says the same thing
                // about the same height, in the proof rather than the model;
                // see the install initialiser.
                //
                // Bit k has weight 2^k because a height with a sign bit is
                // turned away before we get here; see height_bits_citable.
                auto highest_bit_shift = std::get<0>(get_bits_encoding_coeffs(0_i, _height_ub[i]));
                std::vector<ProofFlag> cc;
                if (_height_bits_citable) {
                    auto height_var = std::get<SimpleIntegerVariableID>(_heights[i]);
                    for (Integer k = 0_i; k <= highest_bit_shift; ++k)
                        cc.push_back(model.create_proof_flag_values_fully_reifying(_constraint_id,
                            std::vector<long long>{static_cast<long long>(i), static_cast<long long>(j), k.raw_value}, "scc",
                            WPBSum{} + 1_i * *active + 1_i * ProofBitVariable{height_var, k, true} >= 2_i));
                }
                else {
                    // No bits to conjoin with --- a view height, or one whose
                    // declared bounds put a sign bit in the encoding --- so the
                    // product is linearised the long way, three rows per pair.
                    // The recovery declines such a constraint; see
                    // CumulativeInputs::pair_contribution_bits_are_conjunctions.
                    for (Integer k = 0_i; k <= highest_bit_shift; ++k)
                        cc.push_back(model.names_and_ids_tracker().create_proof_flag_values(
                            _constraint_id, std::vector<long long>{static_cast<long long>(i), static_cast<long long>(j), k.raw_value}, "scc"));
                    auto contrib = contrib_sum_of(cc);
                    model.add_labelled_constraint(_constraint_id, ConstraintProofModelData<Cumulative>::pair_contribution_ge_row_role(i, j),
                        contrib + -1_i * _heights[i] >= 0_i, HalfReifyOnConjunctionOf{*active});
                    model.add_labelled_constraint(_constraint_id, ConstraintProofModelData<Cumulative>::pair_contribution_le_row_role(i, j),
                        contrib + -1_i * _heights[i] <= 0_i, HalfReifyOnConjunctionOf{*active});
                    model.add_labelled_constraint(_constraint_id, ConstraintProofModelData<Cumulative>::pair_contribution_zero_row_role(i, j),
                        contrib <= 0_i, HalfReifyOnConjunctionOf{! *active});
                }
                for (Integer k = 0_i; k.raw_value < static_cast<long long>(cc.size()); ++k)
                    load += power2(k) * cc[k.raw_value];
            }
        }

        auto role = ConstraintProofModelData<Cumulative>::checkpoint_row_role(j);
        if (is_constant_variable(_capacity))
            model.add_labelled_constraint(_constraint_id, role, move(load) <= _capacity_val - fixed_load);
        else
            model.add_labelled_constraint(_constraint_id, role, move(load) + -1_i * _capacity <= -fixed_load);
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
                                        before_flags = _before_flags, after_flags = _after_flags, active_flags = _active_flags,
                                        contrib_flags = _contrib_flags, task_heights = _heights, presence = _presence, per_task_t_lo = _per_task_t_lo,
                                        in_proof = _per_time_flags_in_proof, end_ge_lines](State &, auto &, ProofLogger * const logger) -> void {
        if (! logger || logger->get_assertion_level() > AssertionLevel::Off)
            return;
        auto & tracker = logger->names_and_ids_tracker();

        // #780 step 10: where the per-(task, time) flags were only *named* by
        // define_proof_model, this is where they are defined --- the same two
        // halves the encoder would have written as OPB rows, emitted as `red`
        // steps instead, and registered so that reification_half hands citers
        // the lines rather than labels that do not exist.
        //
        // The order matters: every definition goes out before anything below
        // cites one, and the bridge lemmas below cite `after`.
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

        // The bridge lemma `end >= t+1 -> after`, where the flags are model
        // objects and so all of them exist already:
        //   pol( after[f] : ~after -> s+l <= t )  +  ( end <= s+l )
        //   = ( M.after - end + t >= 0 ).
        // The s+l bits cancel exactly, leaving a single-variable-in-end
        // handle that makes the propagator's after pin RUP-closable even
        // though after is reified on the two-variable s+l. end_le is the
        // cancelling term.
        //
        // Nothing publishes these: they go out at Top over exactly the
        // (i, t) pairs this constraint gave the task a window for, so unit
        // propagation finds them for whoever pins one of those flags. Under
        // #780's in-proof flags the same lemma is emitted per point by the
        // definer below instead, because citing `after` here would drag
        // every definition into existence.
        if (! in_proof)
            for (auto i : active_tasks) {
                if (! ends[i].has_value() || ! end_le[i].has_value())
                    continue;
                for (const auto & after : after_flags[i]) {
                    PolBuilder lemma;
                    lemma.add(reification_half(tracker, after, ReificationHalf::ImpliedBy));
                    lemma.add(*end_le[i]);
                    lemma.emit(*logger, ProofLevel::Top);
                }
            }

        // #780 step 10: rather than defining every per-(task, time) flag
        // here --- a horizon's worth of `red` steps, which is the cost this
        // encoding exists to remove --- publish a definer and let the
        // tracker call it for the keys something actually cites. The names
        // went out with the model and are free; only the definitions are
        // paid for, and only where a rule reasons.
        //
        // Keyed on the activity flag's key, since all three flags and any
        // contribution bits for one (task, time) are defined together and
        // any of them being cited means the others are about to be.
        if (in_proof)
            tracker.publish_flag_definer(id, [=, &tracker](ProofLogger & definer_logger, const ProofFlagKey & key) {
                if (key.values.size() != 2)
                    return;
                auto i = static_cast<std::size_t>(key.values[0]);
                auto t = Integer{key.values[1]};
                if (i >= active_flags.size() || t < per_task_t_lo[i])
                    return;
                auto k = static_cast<std::size_t>((t - per_task_t_lo[i]).raw_value);
                if (k >= active_flags[i].size())
                    return;
                auto define = [&](const ProofFlag & flag, const WPBSumLE & says) {
                    auto [implies, implied_by] = definer_logger.emit_red_proof_lines_reifying(says, flag, ProofLevel::Top);
                    tracker.register_in_proof_reification(flag, implies, implied_by);
                };
                define(before_flags[i][k], per_time_before_says(starts[i], t));
                define(after_flags[i][k], per_time_after_says(starts[i], lengths[i], t));
                define(active_flags[i][k], per_time_active_says(before_flags[i][k], after_flags[i][k], presence[i]));

                // A variable height's contribution bits. In the model
                // these need three rows, because `contrib = h * cact`
                // is a product and the rows are what linearise it. Here
                // they need none: bit by bit the product *is* a
                // conjunction,
                //
                //     cc_{i,t,k}  <->  cact_{i,t}  /\  bit_k(h_i)
                //
                // --- if the task is active its contribution is its
                // height, so bit for bit; if it is not, every bit is
                // zero. Each one is then a two-way reification of a
                // fresh flag over literals that already exist, the same
                // primitive the activity flag above uses, and the three
                // rows fall out of these rather than being asserted
                // beside them.
                //
                // Weight 2^k is bit k because the gate on this requires
                // a height with no sign bit; see height_bits_citable.
                if (! is_constant_variable(task_heights[i])) {
                    const auto & cc = contrib_flags[i][k];
                    auto height_var = std::get<SimpleIntegerVariableID>(task_heights[i]);
                    for (Integer b = 0_i; b.raw_value < static_cast<long long>(cc.size()); ++b)
                        define(cc[b.raw_value], WPBSum{} + 1_i * active_flags[i][k] + 1_i * ProofBitVariable{height_var, b, true} >= 2_i);

                    // And the `cge` row those definitions imply, for the
                    // energy rules and donor_view, which ask for it by
                    // role and should not have to know it is derived
                    // here rather than asserted in the model.
                    //
                    //   ~cact \/ ~bit_b(h) \/ cc_b   (rup, off cc_b's
                    //                                 own reverse half)
                    //
                    // summed at 2^b is `S.~cact - h + Sum cc >= 0`,
                    // which is that row with S as its guard coefficient.
                    PolBuilder cge;
                    for (Integer b = 0_i; b.raw_value < static_cast<long long>(cc.size()); ++b)
                        cge.add(
                            definer_logger.emit_rup_proof_line(
                                WPBSum{} + 1_i * ! active_flags[i][k] + 1_i * ! ProofBitVariable{height_var, b, true} + 1_i * cc[b.raw_value] >= 1_i,
                                ProofLevel::Top),
                            power2(b));
                    tracker.publish_derived_line(
                        id, ConstraintProofModelData<Cumulative>::contribution_ge_row_role(i, t), cge.emit(*logger, ProofLevel::Top));
                }

                // And the bridge lemma `end >= t+1 -> after` for this point:
                //   pol( after[f] : ~after -> s+l <= t )  +  ( end <= s+l )
                //   = ( M.after - end + t >= 0 ).
                // The s+l bits cancel exactly, leaving a single-variable-in-end
                // handle that makes the propagator's after pin RUP-closable even
                // though after is reified on the two-variable s+l. end_le is the
                // cancelling term.
                //
                // It belongs here rather than in a loop of its own: it cites
                // `after`, so a loop over the window would drag every definition
                // into existence and there would be nothing left to be lazy about.
                // Nothing publishes it, because it goes out at Top for exactly
                // the (i, t) something asked for, and unit propagation finds it
                // for whoever pins that flag.
                if (ends[i].has_value() && end_le[i].has_value()) {
                    PolBuilder lemma;
                    lemma.add(reification_half(tracker, after_flags[i][k], ReificationHalf::ImpliedBy));
                    lemma.add(*end_le[i]);
                    lemma.emit(definer_logger, ProofLevel::Top);
                }
            });
    });

    // One cache, shared between the differential check below and the
    // propagator, so an inference cites the line the check passed on.
    auto encoding = _encoding.value_or(default_cumulative_encoding());
    auto recovery_cache = (encoding == CumulativeEncoding::BothRecovering || encoding == CumulativeEncoding::StartCheckpoint)
        ? make_shared<CheckpointRecoveryCache>()
        : nullptr;

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
        .checkpoint_recovery = recovery_cache,
        .pair_contribution_bits_are_conjunctions = _height_bits_citable,
        .per_time_contribution_bits_are_conjunctions = _per_time_flags_in_proof,
        .rules = _rules,
        .proof_mutation = _proof_mutation,
        .presence_mutation = _presence_mutation,
        .overload_tasks = move(_overload_tasks),
        .time_slot_prefix = move(_time_slot_prefix),
        .time_slot_lo = _time_slot_lo,
        .guarded_energy =
            std::make_shared<std::map<std::tuple<size_t, Integer, Integer, Integer, Integer, Integer>, window_energy::GuardedWindowEnergy>>()};

    // #780: let anyone who can name this constraint ask for a capacity row it
    // no longer has an OPB label for. A derived Cumulative built on this one as
    // a donor is the consumer that needs it --- under
    // CumulativeEncoding::StartCheckpoint there is no `cap_<t>` row for it to
    // find, and without this it would decline and take the presolver's whole
    // inference with it, quietly, since a decline there is a supported outcome
    // rather than an error.
    //
    // From an initialiser because that is the earliest point with a logger, and
    // because initialisers run before presolvers (#658) --- the same timing
    // publish_derived_line relies on. A copy of the inputs, as the differential
    // below takes: the propagator's own is about to be moved from. The copy is
    // read-only afterwards, and the cache it shares is a shared_ptr, so a row
    // derived through here and one derived by the propagator are the same row
    // and are paid for once.
    //
    // Published whenever the recovery is switched on at all, not only under
    // StartCheckpoint: where the block is still written the label is found
    // first and this is never reached, so there is nothing to gate.
    if (recovery_cache)
        propagators.install_initialiser([family_inputs = make_shared<CumulativeInputs>(inputs)](State &, auto &, ProofLogger * const logger) -> void {
            if (! logger)
                return;
            logger->names_and_ids_tracker().publish_derived_line_family(family_inputs->owner,
                ConstraintProofModelData<Cumulative>::capacity_row_family(),
                [family_inputs](ProofLogger & deriver_logger, Integer t) -> std::optional<ProofLine> {
                    return recover_cumulative_capacity_row(deriver_logger, *family_inputs, *family_inputs->checkpoint_recovery, t);
                });
        });

    // #780's differential, under CumulativeEncoding::BothRecovering: derive
    // every capacity row from the start-checkpoint rows and check it against
    // the one the model still carries. A copy of the inputs rather than a
    // reference into the propagator's, which is about to be moved from --- the
    // check runs once, before search, and the copy dies with it.
    if (encoding == CumulativeEncoding::BothRecovering)
        propagators.install_initialiser(
            [recovery_inputs = make_shared<CumulativeInputs>(inputs)](State &, auto &, ProofLogger * const logger) -> void {
                if (! logger || logger->get_assertion_level() > AssertionLevel::Off)
                    return;
                check_recovered_cumulative_capacity_rows(*logger, *recovery_inputs, *recovery_inputs->checkpoint_recovery);
            });

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
    // #780 step 10: the per-(task, time) flags are named with the model but may
    // only be *defined* on demand, so every use goes through an accessor that
    // asks for the definition first. The tracker does nothing where there is no
    // definer, which is every encoding but StartCheckpoint, and nothing on a
    // second ask. These shadow the raw vectors deliberately: a bare
    // `before_flags[i][k]` no longer compiles, so the compiler finds a citation
    // that forgot rather than veripb finding it later.
    const auto & before_flags_raw = inputs.before_flags;
    const auto & after_flags_raw = inputs.after_flags;
    const auto & active_flags_raw = inputs.active_flags;
    const auto & contrib_flags_raw = inputs.contrib_flags;
    auto ensure_flags_defined = [&](size_t i, size_t idx) {
        if (logger)
            logger->names_and_ids_tracker().ensure_flag_defined(inputs.owner,
                ConstraintProofModelData<Cumulative>::active_flag_key(i, inputs.per_task_t_lo[i] + Integer{static_cast<long long>(idx)}), *logger);
    };
    auto before_flag = [&](size_t i, size_t idx) -> const ProofFlag & {
        ensure_flags_defined(i, idx);
        return before_flags_raw[i][idx];
    };
    auto after_flag = [&](size_t i, size_t idx) -> const ProofFlag & {
        ensure_flags_defined(i, idx);
        return after_flags_raw[i][idx];
    };
    auto active_flag = [&](size_t i, size_t idx) -> const ProofFlag & {
        ensure_flags_defined(i, idx);
        return active_flags_raw[i][idx];
    };
    auto contrib_bits = [&](size_t i, size_t idx) -> const std::vector<ProofFlag> & {
        ensure_flags_defined(i, idx);
        return contrib_flags_raw[i][idx];
    };
    // A whole task's row, for a caller that hands it to shared machinery which
    // indexes it itself. Every point of the row is defined first, so this is
    // the one accessor whose cost is the window rather than a point --- give it
    // the clipped window where there is one.
    auto flag_row = [&](const std::vector<std::vector<ProofFlag>> & family, size_t i) -> const std::vector<ProofFlag> & {
        for (size_t k = 0; k < family[i].size(); ++k)
            ensure_flags_defined(i, k);
        return family[i];
    };
    const auto & per_task_t_lo = inputs.per_task_t_lo;
    const auto & per_task_t_hi = inputs.per_task_t_hi;
    const auto & end_ge_lines = inputs.end_ge_lines;
    const auto & capacity_lines = inputs.capacity_lines;

    // Where a citer gets the row saying the load at `t` is within the capacity.
    // Today that is the OPB row the time-indexed block wrote, unless #780's
    // recovery is on, in which case it is derived from the start-checkpoint
    // rows instead --- once per time point, cached, and reason-free at Top, so
    // the second citer of a point pays nothing and backtracking does not lose
    // it. The recovery declines a Cumulative it cannot yet speak about (a
    // variable height, an optional task), and the model row is what is left.
    //
    // The time-table family goes through this --- the overflow contradiction
    // and both bound pushes --- and so do the overload check's (OC)/(TTOC)
    // window supply and the (TTHE-OC)/(KAOC) per-time availability lines, the
    // latter being the only citer that uses a row as the base of a per-point
    // sub-derivation rather than summing it straight into a pol, and so does
    // edge-finding's window supply --- and with it TTEF, the energetic form and
    // our own not-first / not-last, which is certified by edge-finding's
    // certificate unchanged, and so does the published not-first / not-last,
    // the only citer that scales the row rather than adding it at one. That is
    // every citer in this file. What is left is outside it:
    // derived_cumulative.cc still looks its donors' rows up by label, which is
    // the rest of #780. A lane whose every rule has moved joins the
    // `startcheckpoint` ctest arm, which is where that progress is measured.
    auto capacity_row = [&](Integer t) -> std::optional<ProofLine> {
        if (logger && inputs.checkpoint_recovery)
            if (auto recovered = recover_cumulative_capacity_row(*logger, inputs, *inputs.checkpoint_recovery, t))
                return recovered;
        auto line = capacity_lines.find(t);
        if (line == capacity_lines.end())
            return std::nullopt;
        return line->second;
    };
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
        return window_energy::Task{std::get<SimpleIntegerVariableID>(starts[i]), llb(i), per_task_t_lo[i], flag_row(before_flags_raw, i),
            flag_row(after_flags_raw, i), flag_row(active_flags_raw, i),
            l_is_var(i) ? make_optional(std::get<SimpleIntegerVariableID>(lengths_var[i])) : optional<SimpleIntegerVariableID>{}};
    };

    // What a variable-height task is guaranteed to contribute at one time
    // point, as a term over the contribution bits a capacity row carries:
    // `contrib >= lb(h)` unless the task is not active there. #686's line,
    // reached from here rather than from a donor view.
    auto guaranteed_contribution = [&](const ReasonLiterals & reason, size_t i, Integer t) -> ProofLine {
        auto & tracker = logger->names_and_ids_tracker();
        auto row = tracker.constraint_row(owner, ConstraintProofModelData<Cumulative>::contribution_ge_row_role(i, t));
        // Emitted alongside the flags, so a task with a window here has one.
        // Missing means the flags and the rows have come apart, which is worth
        // saying here rather than as a rejected proof later.
        if (! row)
            throw ProofError{"cumulative: task " + std::to_string(i) + " has no contribution row at time " + std::to_string(t.raw_value)};
        auto fi = static_cast<size_t>((t - per_task_t_lo[i]).raw_value);
        return guaranteed_contribution_row(*logger, &reason, contrib_bits(i, fi), active_flag(i, fi),
            std::get<SimpleIntegerVariableID>(heights_var[i]), hlb(i), ProofLine{*row}, ProofLevel::Temporary);
    };

    // An energy row as the capacity lines want it: the line to add to a pol
    // whose other terms are C_t's, and the coefficient to add it at.
    //
    // For a constant height that is the row itself scaled by h, and its
    // `active` terms cancel against C_t's directly. A variable height is not in
    // C_t at all --- what is there is the bit-linearised contribution --- so
    // the row is converted first: one guaranteed_contribution line per time
    // point of its window, plus the row at lb(h). The activity cancels
    // *between those two*, each conversion line carrying `lb(h)·~active` where
    // the scaled row carries `lb(h)·active`, and what is left is
    //
    //     Sum_t contrib_t  >=  lb(h) · bound
    //
    // which is what cancels against C_t. Anything else the row carried --- a
    // guarded row's guard literals --- rides through at the same scale, so a
    // citer discharges them exactly as it would have.
    //
    // The window has to be the row's own *clipped* one and not the requested
    // one: the conversion lines have to cover exactly the time points the row's
    // sum runs over, or the cancellation is partial and the pol is left open.
    auto energy_contribution = [&](const ReasonLiterals & reason, size_t i, ProofLine energy_line, Integer lo,
                                   Integer hi) -> std::pair<ProofLine, Integer> {
        if (! h_is_var(i))
            return {energy_line, hlb(i)};
        PolBuilder pol;
        for (Integer t = lo; t < hi; ++t)
            pol.add(guaranteed_contribution(reason, i, t));
        pol.add(energy_line, hlb(i));
        return {pol.emit(*logger, ProofLevel::Temporary), 1_i};
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
        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * before_flag(i, fi) >= 1_i, ProofLevel::Temporary);
        // A mandatory task has s_i + l_i ≥ lb(s_i) + lb(l_i) > t.
        materialise_after_sum(i, state.lower_bound(starts[i]));
        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * after_flag(i, fi) >= 1_i, ProofLevel::Temporary);
        auto active_line = logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * active_flag(i, fi) >= 1_i, ProofLevel::Temporary);
        if (! h_is_var(i))
            return {active_line, hlb(i)};
        auto contrib_line = logger->emit_rup_proof_line_under_reason(reason, contrib_sum_of(contrib_bits(i, fi)) >= hlb(i), ProofLevel::Temporary);
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
                std::to_string(per_task_t_lo[i].raw_value) + " for " + std::to_string(active_flags_raw[i].size()) + ")"};
        return inputs.guarded_energy->emplace(key, *derived).first->second;
    };

    // Which of the pushed task's two guards its firing has to discharge. The
    // other one is the negated conclusion, and the wrapping RUP refutes it.
    enum class GuardToDischarge
    {
        Low,
        High
    };

    // What the energetic form charges a window with: one task, and the two
    // guards its own bounds put on the row that says how much of it the window
    // must contain. Unlike the contained-task rows the other forms cite, these
    // are keyed on bounds that move --- a contained task's guards come from the
    // window and are the same at every node, a non-contained one's do not ---
    // which is the reuse question #755 leaves open and this deliberately does
    // not try to answer. Correctness first: the guards are exactly the start
    // bounds `guaranteed()` asked `window_energy_bound` about, so the row
    // establishes exactly the energy the detection counted.
    struct EnergeticContributor
    {
        std::size_t task;
        Integer low_guard, high_guard;
        /// Whether the window contains this task, which is what tells the two
        /// mutation lanes apart: dropping a contained task's row corrupts a
        /// row plain edge-finding would have cited too, and dropping a
        /// non-contained one corrupts the only energy this rule adds.
        bool contained;
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
                                          Integer pushed_high_guard, GuardToDischarge discharge,
                                          const vector<EnergeticContributor> & energetic = {}) {
        return [&, a, b, inside_tasks, pushed, pushed_low_guard, pushed_high_guard, discharge, energetic](const ReasonLiterals & reason) -> void {
            if (! logger)
                return;

            PolBuilder pol;
            for (Integer t = a; t < b; ++t) {
                if (std::holds_alternative<cumulative_proof_mutation::OmitCapacityLine>(mutation) && t == b - 1_i)
                    continue;
                if (auto line = capacity_row(t))
                    pol.add(*line);
            }

            auto cite = [&](size_t i, Integer low_guard, Integer high_guard, bool discharge_low, bool discharge_high) {
                const auto & row = guarded_energy(i, a, b, low_guard, high_guard);
                auto [contribution_line, coeff] = energy_contribution(reason, i, row.line, row.lo, row.hi);
                pol.add(contribution_line, coeff);
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

            // The energetic form charges the window every task's guaranteed
            // energy, so it cites a row per candidate rather than a row per
            // contained task plus a pin per profile time point. Both of each
            // row's guards are the task's own current bounds, which the reason
            // carries whether or not the window contains it --- so unlike
            // TTEF's profile term this needs no pins at all, which is what
            // #755 said it would not.
            //
            // The bounds are the ones the sweep captured when it built its
            // candidates, not the live ones: an earlier push in the same sweep
            // may have tightened them, and a guard at the stale bound is one
            // the reason still entails. It is also the bound the detection's
            // arithmetic used, so the row establishes neither more nor less
            // than was counted.
            if (! energetic.empty()) {
                auto skip_outside = std::holds_alternative<cumulative_proof_mutation::DropEnergeticContributor>(mutation);
                auto skip_inside = std::holds_alternative<cumulative_proof_mutation::DropContainedTask>(mutation);
                for (const auto & e : energetic) {
                    if (e.task == pushed)
                        continue;
                    if (e.contained ? skip_inside : skip_outside) {
                        (e.contained ? skip_inside : skip_outside) = false;
                        continue;
                    }
                    cite(e.task, e.low_guard, e.high_guard, true, true);
                }
            }
            else
                // A contained task is inside the window whichever way the push
                // goes, so both its guards are refuted by the reason. Its high
                // guard is the first start that would take it out of the
                // window, stated against the *clipped* window since that is
                // where the lemma's sum stops; where the two differ the guard
                // is refuted by the task's declared bounds rather than by the
                // search, and the RUP closes on those just the same.
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
            if (rules.time_table_edge_finding && energetic.empty()) {
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
        logger->emit_rup_proof_line_under_reason(reason, plus_ext(WPBSum{} + 1_i * before_flag(j_idx, fj), ext, 1_i) >= 1_i, ProofLevel::Temporary);
        // s_lo_after + lb(l_j) ≥ t+1 gives after_{j,t} = 1 (under ¬ext
        // for ub-push, under the running bound for lb-push).
        materialise_after_sum(j_idx, s_lo_after);
        logger->emit_rup_proof_line_under_reason(reason, plus_ext(WPBSum{} + 1_i * after_flag(j_idx, fj), ext, 1_i) >= 1_i, ProofLevel::Temporary);
        auto active_line = logger->emit_rup_proof_line_under_reason(
            reason, plus_ext(WPBSum{} + 1_i * active_flag(j_idx, fj), ext, 1_i) >= 1_i, ProofLevel::Temporary);
        if (! h_is_var(j_idx))
            return {active_line, hlb(j_idx)};
        auto contrib_line = logger->emit_rup_proof_line_under_reason(
            reason, plus_ext(contrib_sum_of(contrib_bits(j_idx, fj)), ext, hlb(j_idx)) >= hlb(j_idx), ProofLevel::Temporary);
        return {contrib_line, 1_i};
    };

    // --- #746: the published not-first / not-last detection -----------------
    //
    // `not_first_not_last` above asks what the guarded window-energy lemma can
    // *derive*: the least overlap the pushed task can have with the window over
    // the negated conclusion's whole start range. Schutt & Wolf (CP 2010,
    // Proposition 1) and Kameugne et al. (CPAIOR 2018, rule (NF)) charge the
    // overlap at *one end* of that range instead, over the contained set's own
    // window `[est(Omega), lct(Omega))`:
    //
    //     e(Omega) + c_j * (min(ect_j, lct(Omega)) - est(Omega))
    //         > C * (lct(Omega) - est(Omega))         =>  s_j >= ECT(Omega)
    //
    // and the mirror. That is more than the lemma derives, so it is not a
    // window-energy argument at all, and this is what it is instead.
    //
    // **Contiguity.** Every task in Omega has `ect_k >= ECT(Omega)`, so it
    // cannot finish before `ECT(Omega)`: if it is running at any time in
    // `[est(Omega), ECT(Omega))` it is still running at the end of that
    // interval. In the encoding that is one line per (task, time),
    //
    //     active_{k,u}  =>  active_{k,v}      for  u <= v < ECT(Omega)
    //
    // since `before` is monotone in the model and `after_{k,v}` follows from
    // the reason's `s_k >= est_k` and `l_k >= p_k`. So the whole prefix's load
    // from Omega is capped by the load at one time point --- and if the pushed
    // task is running *there*, the capacity row at that one point caps the
    // prefix at `C - c_j` rather than `C`. Summed over the window that is
    // exactly the published inequality, which is #746's answer to why the rule
    // is sound: contiguity plus `ECT` at a single time point, not window
    // energy.
    //
    // **Where the pushed task is running.** It is running at `v` when
    // `s_j <= v` (the negated conclusion, which gives `s_j <= ECT(Omega) - 1`)
    // and `s_j + l_j >= v + 1` (the reason's `s_j >= lb(s_j)`, which reaches
    // `ect_j`). Both hold at `v = ECT(Omega) - 1` exactly when
    // `ect_j >= ECT(Omega)`, and then one pol does the whole rule. When
    // `ect_j < ECT(Omega)` no single time point works --- the meeting point is
    // `s_j` itself, which is a variable --- so the derivation becomes a chain,
    // walking the bound up `p_j` at a time in the way the time-table push
    // already does, each rung's row weakened by that rung's own conclusion and
    // deposited under the reason for the next rung's unit propagation. Every
    // rung charges the window at least what the detection counted, so the first
    // one already suffices and the rest only carry the bound the rest of the
    // way.
    //
    // Everything is stated in *activity* space rather than in the
    // bit-linearised contribution space the capacity rows use, because
    // contiguity is a statement about activity. A variable-height task's
    // capacity term is converted back with the same `guaranteed_contribution`
    // line `energy_contribution` would have used to convert the other way; the
    // count is the same either way.
    struct PublishedTask
    {
        std::size_t task;
        Integer est, ub, length;
    };

    // active_{k,v} >= active_{k,u}: task k, running at u, is still running at
    // v. `forward` is not-first's direction (u <= v, the far end pinned by
    // `after`); its mirror pins `before` instead. nullopt when one of the two
    // times is outside k's flag range, where there is no activity term to
    // bound and nothing to say.
    auto contiguity_applies = [&](const PublishedTask & k, Integer u, Integer v) {
        auto t_lo = per_task_t_lo[k.task], t_hi = per_task_t_hi[k.task];
        return u >= t_lo && u <= t_hi && v >= t_lo && v <= t_hi;
    };
    auto published_contiguity = [&](const ReasonLiterals & reason, const PublishedTask & k, Integer u, Integer v, bool forward) -> ProofLine {
        auto t_lo = per_task_t_lo[k.task];
        auto fu = static_cast<size_t>((u - t_lo).raw_value), fv = static_cast<size_t>((v - t_lo).raw_value);
        if (forward) {
            // s_k + l_k >= est_k + p_k = ect_k >= ECT(Omega) > v.
            materialise_after_sum(k.task, k.est);
            logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * after_flag(k.task, fv) >= 1_i, ProofLevel::Temporary);
        }
        else
            // s_k <= ub(s_k) <= LST(Omega) <= v.
            logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * before_flag(k.task, fv) >= 1_i, ProofLevel::Temporary);
        return logger->emit_rup_proof_line_under_reason(
            reason, WPBSum{} + 1_i * active_flag(k.task, fv) + 1_i * ! active_flag(k.task, fu) >= 1_i, ProofLevel::Temporary);
    };

    // The pushed task pinned active at t, in activity space: `pin_pushed`'s
    // three lines, but returning the `active` one rather than the contribution
    // one, since this rule's capacity rows have been converted to match.
    auto published_pin = [&](const ReasonLiterals & reason, size_t j_idx, Integer t, const ExtLits & ext, Integer s_lo_after) -> ProofLine {
        // The chain's own stop rules keep every rung inside the pushed task's
        // flag range, so a time outside it means the rung arithmetic and the
        // flags have come apart. Worth saying here rather than as a rejected
        // proof, or a flag lookup that reads past the end.
        if (t < per_task_t_lo[j_idx] || t > per_task_t_hi[j_idx])
            throw ProofError{
                "cumulative published not-first / not-last: task " + std::to_string(j_idx) + " has no flag at time " + std::to_string(t.raw_value)};
        auto fj = static_cast<size_t>((t - per_task_t_lo[j_idx]).raw_value);
        logger->emit_rup_proof_line_under_reason(reason, plus_ext(WPBSum{} + 1_i * before_flag(j_idx, fj), ext, 1_i) >= 1_i, ProofLevel::Temporary);
        materialise_after_sum(j_idx, s_lo_after);
        logger->emit_rup_proof_line_under_reason(reason, plus_ext(WPBSum{} + 1_i * after_flag(j_idx, fj), ext, 1_i) >= 1_i, ProofLevel::Temporary);
        return logger->emit_rup_proof_line_under_reason(
            reason, plus_ext(WPBSum{} + 1_i * active_flag(j_idx, fj), ext, 1_i) >= 1_i, ProofLevel::Temporary);
    };

    auto published_nfnl_justification = [&](Integer a2, Integer b, const vector<PublishedTask> & theta, size_t j, Integer j_lb, Integer j_ub,
                                            Integer boundary, bool not_first) {
        return [&, a2, b, theta, j, j_lb, j_ub, boundary, not_first](const ReasonLiterals & reason) -> void {
            if (! logger)
                return;
            logger->emit_proof_comment("cumulative published not-" + string{not_first ? "first" : "last"} + " w=" + std::to_string(theta.size()) +
                " span=" + std::to_string((b - a2).raw_value));

            if (std::holds_alternative<cumulative_proof_mutation::PublishedEmitNothing>(mutation))
                return;

            auto p_j = llb(j), h_j = hlb(j);
            auto drop_pin = std::holds_alternative<cumulative_proof_mutation::DropPublishedPin>(mutation);
            auto drop_task = std::holds_alternative<cumulative_proof_mutation::DropContainedTask>(mutation);
            auto omit_capacity = std::holds_alternative<cumulative_proof_mutation::OmitCapacityLine>(mutation);

            // A capacity line with the contained set's and the pushed task's
            // contributions converted back into activity, so contiguity has
            // something to cancel against. Any other task's ride through as the
            // negative terms they already are.
            auto capacity_at = [&](PolBuilder & pol, Integer t, Integer coeff) {
                if (omit_capacity && t == b - 1_i)
                    return;
                auto line = capacity_row(t);
                if (! line)
                    return;
                pol.add(*line, coeff);
                auto convert = [&](size_t i) {
                    if (h_is_var(i) && t >= per_task_t_lo[i] && t <= per_task_t_hi[i])
                        pol.add(guaranteed_contribution(reason, i, t), coeff);
                };
                for (const auto & k : theta)
                    convert(k.task);
                convert(j);
            };

            // The contained set's energy over [a2, b), in activity space: the
            // same guarded rows edge-finding cites, at the same guards, over a
            // window keyed on est(Omega) rather than on the swept one.
            auto add_theta_energy = [&](PolBuilder & pol) {
                for (const auto & k : theta) {
                    if (drop_task && k.task == theta.front().task)
                        continue;
                    const auto & row =
                        guarded_energy(k.task, a2, b, clipped_window_start(k.task, a2), clipped_window_end(k.task, b) - k.length + 1_i);
                    pol.add(row.line, hlb(k.task));
                    if (row.low_coeff > 0_i)
                        pol.add(logger->emit_rup_proof_line_under_reason(
                                    reason, WPBSum{} + 1_i * (starts[k.task] >= row.low_guard) >= 1_i, ProofLevel::Temporary),
                            hlb(k.task) * row.low_coeff);
                    if (row.bound > 0_i)
                        pol.add(logger->emit_rup_proof_line_under_reason(
                                    reason, WPBSum{} + 1_i * (starts[k.task] < row.high_guard) >= 1_i, ProofLevel::Temporary),
                            hlb(k.task) * row.bound);
                    if (row.length_coeff > 0_i)
                        pol.add(logger->emit_rup_proof_line_under_reason(
                                    reason, WPBSum{} + 1_i * (lengths_var[k.task] >= row.length_guard) >= 1_i, ProofLevel::Temporary),
                            hlb(k.task) * row.length_coeff);
                }
            };

            // The published charge. Non-positive means the detection fired on
            // the contained set alone overflowing the window, where there is no
            // pushed task to place and the energy rows against the capacity
            // rows are the whole argument.
            auto charge = not_first ? min(j_lb + p_j, b) - a2 : b - max(j_ub, a2);
            if (charge <= 0_i) {
                PolBuilder pol;
                add_theta_energy(pol);
                for (Integer t = a2; t < b; ++t)
                    capacity_at(pol, t, 1_i);
                pol.emit(*logger, ProofLevel::Temporary);
                return;
            }

            // One rung of the chain. `meet` is the time point the capped range
            // is compared against, `capped` the half-open range the rung caps
            // at `C - c_j`, and `ext` the rung's own conclusion, which every
            // line it lays down is weakened by.
            auto rung = [&](Integer meet, Integer capped_lo, Integer capped_hi, const ExtLits & ext, Integer s_lo_after) {
                PolBuilder pol;
                add_theta_energy(pol);

                auto multiplicity = not_first ? meet + 1_i - a2 : b - meet;
                capacity_at(pol, meet, multiplicity);
                if (! drop_pin)
                    pol.add(published_pin(reason, j, meet, ext, s_lo_after), multiplicity * h_j);

                for (const auto & k : theta) {
                    auto from = not_first ? a2 : meet + 1_i, to = not_first ? meet : b;
                    for (Integer u = from; u < to; ++u)
                        // A time outside the task's flag range has no activity
                        // term in the capacity row either, so there is nothing
                        // to bound and nothing to say.
                        if (contiguity_applies(k, u, meet))
                            pol.add(published_contiguity(reason, k, u, meet, not_first), hlb(k.task));
                }

                // The times the rung does not reach through `meet`: the pushed
                // task is running at each of them under the rung's own case, so
                // each is capped directly.
                for (Integer u = not_first ? meet + 1_i : capped_lo; u < (not_first ? capped_hi : meet); ++u) {
                    capacity_at(pol, u, 1_i);
                    if (! drop_pin)
                        pol.add(published_pin(reason, j, u, ext, s_lo_after), h_j);
                }

                // And the rest of the window, at the full capacity.
                for (Integer u = a2; u < b; ++u)
                    if (not_first ? u >= capped_hi : u < capped_lo)
                        capacity_at(pol, u, 1_i);

                pol.emit(*logger, ProofLevel::Temporary);
            };

            // The chain, walking the bound `p_j` at a time. It stops on
            // whichever comes first: the target, or a running bound the reason
            // already contradicts --- the deposits and the reason are then
            // jointly unsatisfiable, so the framework's wrapping RUP has
            // everything it needs and a further rung would be asking for an
            // order literal outside the task's own domain.
            if (not_first) {
                auto running = j_lb;
                while (true) {
                    auto meet = min(running + p_j - 1_i, boundary - 1_i);
                    auto next = meet + 1_i;
                    rung(meet, a2, min(running + p_j, b), ExtLits{starts[j] >= next}, running);
                    if (next >= boundary || next > j_ub)
                        break;
                    logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (starts[j] >= next) >= 1_i, ProofLevel::Temporary);
                    running = next;
                }
            }
            else {
                auto running = j_ub;
                auto target = boundary - p_j + 1_i;
                while (true) {
                    auto meet = max(running, boundary);
                    auto next = meet - p_j + 1_i;
                    rung(meet, max(a2, running), b, ExtLits{starts[j] < next}, next);
                    if (next <= target || next <= j_lb)
                        break;
                    logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (starts[j] < next) >= 1_i, ProofLevel::Temporary);
                    running = next - 1_i;
                }
            }
        };
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
                pol.add(*capacity_row(violating_t));
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
            // A task guaranteed no duration, or no demand, carries no
            // guaranteed energy, so there is nothing for the lemma to establish
            // and nothing for the window to be charged. Only reachable for a
            // variable one --- a constant this small was turned away at prepare
            // time --- and it can stop being true further down the search,
            // which is why it is asked here and not there.
            if (llb(i) <= 0_i || hlb(i) <= 0_i)
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
            Integer energy = 0_i, inside_mandatory = 0_i, min_ect = 0_i, max_lst = 0_i, min_est = 0_i;
            vector<size_t> inside_tasks;
            // The same set again, with the bounds the published condition's
            // certificate argues about, and only collected when something asks
            // for them. Captured here rather than read back out of `state` in
            // the justification: by then an earlier push has landed, and the
            // state holds a bound the reason does not support.
            vector<PublishedTask> published_theta;
            for (const auto & c : candidates) {
                if (c.est < a)
                    continue;
                energy += c.energy;
                inside_mandatory += c.mandatory;
                inside_tasks.push_back(c.task);
                if (rules.not_first_not_last_published && logger)
                    published_theta.push_back(PublishedTask{c.task, c.est, c.lct - c.length, c.length});
                if (elastic_rules)
                    join_elastic(c);
                min_ect = inside_tasks.size() == 1 ? c.est + c.length : min(min_ect, c.est + c.length);
                // The papers' window is the contained set's own [est, lct), not
                // the swept one: only the published arm below reads this.
                min_est = inside_tasks.size() == 1 ? c.est : min(min_est, c.est);
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

                // The rows the energetic certificate cites, one per candidate
                // the window can reach. Built once per window rather than once
                // per push: every push over this window cites the same set,
                // minus the task it is pushing.
                //
                // A task with a non-positive bound is left out rather than
                // cited at zero, which is the same clamp `guaranteed` applies:
                // the lemma has nothing to derive for a task the window cannot
                // reach, and would decline to emit a row at all.
                vector<EnergeticContributor> energetic_contributors;
                if (rules.energetic_edge_finding && logger)
                    for (const auto & c2 : candidates) {
                        auto low_guard = c2.est, high_guard = c2.lct - c2.length + 1_i;
                        if (window_energy::window_energy_bound(
                                c2.length, per_task_t_lo[c2.task], active_flag_count(c2.task), a, b, pair{low_guard, high_guard - 1_i}) <= 0_i)
                            continue;
                        energetic_contributors.push_back(EnergeticContributor{c2.task, low_guard, high_guard, c2.est >= a && c2.lct <= b});
                    }

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
                        auto justify = edge_finding_justification(a, b, inside_tasks, j.task, low_guard, high_guard,
                            starts_inside ? GuardToDischarge::Low : GuardToDischarge::High, energetic_contributors);
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

                        // The published detection instead, verbatim, over the
                        // papers' own window [est(Omega), lct(Omega)). Their
                        // term is the overlap at one end of the negated
                        // conclusion's start range, unclamped against j's far
                        // bound, so it is neither above nor below what the
                        // lemma derives --- and it is certified by contiguity
                        // rather than by that lemma. See
                        // `published_nfnl_justification`, and
                        // CumulativeRules::not_first_not_last_published for
                        // both why it is sound and what it is worth.
                        if (rules.not_first_not_last_published) {
                            auto ect_j = s_lo + p_j, lst_j = j.lct - p_j;
                            auto span = b - min_est;
                            auto one_too_far = std::holds_alternative<cumulative_proof_mutation::PushOneTooFar>(mutation);
                            if (s_lo < min_ect && energy + h_j * (min(ect_j, b) - min_est) > capacity * span) {
                                auto justify = published_nfnl_justification(min_est, b, published_theta, j.task, s_lo, s_hi, min_ect, true);
                                inference.infer_greater_than_or_equal(logger, starts[j.task], one_too_far ? min_ect + 1_i : min_ect,
                                    JustifyExplicitly{justify, ThenRUP::Yes, hints::Cumulative{owner}}, reason_with_presence());
                            }
                            if (max_lst < j.lct && energy + h_j * (b - max(lst_j, min_est)) > capacity * span) {
                                auto justify = published_nfnl_justification(min_est, b, published_theta, j.task, s_lo, s_hi, max_lst, false);
                                inference.infer_less_than(logger, starts[j.task], one_too_far ? max_lst - p_j : max_lst - p_j + 1_i,
                                    JustifyExplicitly{justify, ThenRUP::Yes, hints::Cumulative{owner}}, reason_with_presence());
                            }
                            continue;
                        }

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
                                auto justify = edge_finding_justification(
                                    a, b, inside_tasks, j.task, low_guard, min_ect, GuardToDischarge::Low, energetic_contributors);
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
                                auto justify = edge_finding_justification(
                                    a, b, inside_tasks, j.task, low_guard, s_hi + 1_i, GuardToDischarge::High, energetic_contributors);
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
                                // Asked here rather than below the elastic
                                // branch, which does not use the row: this is
                                // also the test for whether the encoding says
                                // anything about `t` at all, and moving it down
                                // would let a time point with no row take that
                                // branch where today it is skipped outright.
                                // The cost of keeping it here is that a point
                                // which then takes the elastic branch has paid
                                // for a recovery it does not cite --- bounded,
                                // since rows are cached per time point for the
                                // whole constraint, and worth it against
                                // changing behaviour on a branch no fixture
                                // currently reaches.
                                auto capacity_line = capacity_row(t);
                                if (! capacity_line)
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
                                        items.push_back(SubsetSumItem{hlb(j), active_flag(j, static_cast<size_t>((t - per_task_t_lo[j]).raw_value))});
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
                                avail.add(*capacity_line);
                                for (auto j : active_tasks) {
                                    if (t < per_task_t_lo[j] || t > per_task_t_hi[j])
                                        continue;
                                    auto flag = active_flag(j, static_cast<size_t>((t - per_task_t_lo[j]).raw_value));
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
                                                active_flag(i, static_cast<size_t>((t - per_task_t_lo[i]).raw_value))),
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
                    //
                    // The rows come from `capacity_row`, so under #780's
                    // recovering encoding the whole window is supplied from the
                    // start-checkpoint block. The cancellation is unaffected
                    // either way: a recovered row is the *same inequality* as
                    // the model's, over the same candidates at `t` and the same
                    // activity flags, so what a contained task cancels against
                    // does not depend on which of the two produced it. This is
                    // the first citer to want a row at every point of a window
                    // rather than at one, so it is where the recovery's
                    // per-point cost is first paid many times over --- but each
                    // row is derived once for the constraint and cached, so a
                    // second window overlapping the first pays nothing.
                    PolBuilder pol;
                    for (Integer t = a; t < b; ++t) {
                        if (omit_capacity_line && t == b - 1_i)
                            continue;
                        if (auto line = capacity_row(t))
                            pol.add(*line);
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
                                activity += 1_i * active_flag(i, static_cast<size_t>((t - per_task_t_lo[i]).raw_value));
                            line =
                                logger->emit_rup_proof_line_under_reason(reason, move(activity) >= energy_line->bound + 1_i, ProofLevel::Temporary);
                        }
                        auto [contribution_line, coeff] = energy_contribution(reason, i, line, energy_line->lo, energy_line->hi);
                        pol.add(contribution_line, coeff);
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
        pol.add(*capacity_row(t));
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

auto ConstraintProofModelData<Cumulative>::capacity_row_family() -> string
{
    return "cap";
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

auto ConstraintProofModelData<Cumulative>::checkpoint_row_role(size_t task) -> string
{
    // Must stay the string define_proof_model labels the row with.
    return "scap_" + std::to_string(task);
}

auto ConstraintProofModelData<Cumulative>::pair_before_flag_key(size_t i, size_t j) -> ProofFlagKey
{
    return ProofFlagKey{{static_cast<long long>(i), static_cast<long long>(j)}, "sb"};
}

auto ConstraintProofModelData<Cumulative>::pair_after_flag_key(size_t i, size_t j) -> ProofFlagKey
{
    return ProofFlagKey{{static_cast<long long>(i), static_cast<long long>(j)}, "sa"};
}

auto ConstraintProofModelData<Cumulative>::pair_active_flag_key(size_t i, size_t j) -> ProofFlagKey
{
    return ProofFlagKey{{static_cast<long long>(i), static_cast<long long>(j)}, "sact"};
}

auto ConstraintProofModelData<Cumulative>::pair_contribution_flag_key(size_t i, size_t j, Integer bit) -> ProofFlagKey
{
    return ProofFlagKey{{static_cast<long long>(i), static_cast<long long>(j), bit.raw_value}, "scc"};
}

auto ConstraintProofModelData<Cumulative>::pair_contribution_ge_row_role(size_t i, size_t j) -> string
{
    return std::to_string(i) + "_" + std::to_string(j) + "_scge";
}

auto ConstraintProofModelData<Cumulative>::pair_contribution_le_row_role(size_t i, size_t j) -> string
{
    return std::to_string(i) + "_" + std::to_string(j) + "_scle";
}

auto ConstraintProofModelData<Cumulative>::pair_contribution_zero_row_role(size_t i, size_t j) -> string
{
    return std::to_string(i) + "_" + std::to_string(j) + "_scz";
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
