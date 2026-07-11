#include <gcs/constraints/disjunctive/disjunctive.hh>
#include <gcs/constraints/disjunctive/hints.hh>
#include <gcs/constraints/innards/recover_am1.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <algorithm>
#include <functional>
#include <map>
#include <memory>
#include <optional>
#include <sstream>
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

using std::function;
using std::make_pair;
using std::make_shared;
using std::make_unique;
using std::map;
using std::max;
using std::min;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::shared_ptr;
using std::size_t;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

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
}

Disjunctive::Disjunctive(vector<IntegerVariableID> starts, vector<IntegerVariableID> lengths) : _starts(move(starts)), _lengths(move(lengths))
{
    if (_starts.size() != _lengths.size())
        throw InvalidProblemDefinitionException{"Disjunctive: starts and lengths must have the same size"};
    // Constant durations are checked here; variable durations are checked
    // against their root lower bound in prepare().
    for (const auto & l : _lengths)
        if (is_constant_variable(l) && const_value_of(l) < 0_i)
            throw InvalidProblemDefinitionException{"Disjunctive: lengths must be non-negative"};
}

Disjunctive::Disjunctive(vector<IntegerVariableID> starts, vector<Integer> lengths) : Disjunctive(move(starts), as_constant_var_ids(lengths))
{
}

auto Disjunctive::with_strict(std::optional<bool> strict) -> Disjunctive &
{
    _strict = strict.value_or(true);
    return *this;
}

auto Disjunctive::clone() const -> unique_ptr<Constraint>
{
    auto cloned = make_unique<Disjunctive>(_starts, _lengths);
    cloned->with_strict(_strict);
    return cloned;
}

auto Disjunctive::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto Disjunctive::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    auto n = _starts.size();

    // Resolve length snapshots. _length_vals is the constant value (0
    // placeholder for a variable, where _lengths[i] is read from the state);
    // _length_ub is the initial upper bound used to size the window.
    _length_vals.assign(n, 0_i);
    _length_ub.assign(n, 0_i);
    for (size_t i = 0; i < n; ++i) {
        if (is_constant_variable(_lengths[i])) {
            _length_vals[i] = const_value_of(_lengths[i]);
            _length_ub[i] = const_value_of(_lengths[i]);
        }
        else {
            if (initial_state.lower_bound(_lengths[i]) < 0_i)
                throw InvalidProblemDefinitionException{"Disjunctive: lengths must be non-negative"};
            _length_ub[i] = initial_state.upper_bound(_lengths[i]);
        }
    }

    // In non-strict mode, a task that is definitely zero-length cannot constrain
    // any other task, so drop it. A constant zero is dropped here; a variable
    // duration that *can* be zero stays active and gets a zero-length escape
    // flag (it might still take a positive value during search). In strict mode
    // every task participates (a zero-length task may not sit strictly inside
    // another's active interval).
    _active_tasks.reserve(n);
    for (size_t i = 0; i < n; ++i) {
        if (! _strict && is_constant_variable(_lengths[i]) && _length_vals[i] == 0_i)
            continue;
        _active_tasks.push_back(i);
    }

    if (_active_tasks.size() < 2)
        return false;

    // Per-task possible-active window from root bounds. Only meaningful for
    // positive-length tasks; consumers gate on length_ub[i] > 0_i.
    _per_task_t_lo.assign(n, 0_i);
    _per_task_t_hi.assign(n, 0_i);
    for (auto i : _active_tasks) {
        if (_length_ub[i] == 0_i)
            continue;
        auto [s_lo, s_hi] = initial_state.bounds(_starts[i]);
        _per_task_t_lo[i] = s_lo;
        _per_task_t_hi[i] = s_hi + _length_ub[i] - 1_i;
    }

    // Non-strict mode: every variable-duration task gets a zero-length escape
    // in the separation clause, matching cake_pb_cp, which adds the zw
    // disjunct for every variable-length argument regardless of its bounds.
    // Gating it on lower_bound == 0 changes the labelled @c[id][.._sepal1]
    // row's content, and proofs that pol-cite that label then fail to
    // chain-verify (issue #482). An always-positive duration's escape is just
    // statically false; add_escape_pins refutes it in one RUP step. The
    // propagator already ignores zero-mandatory tasks via lb(l).
    _zero_escape.assign(n, 0);
    if (! _strict)
        for (auto i : _active_tasks)
            _zero_escape[i] = is_constant_variable(_lengths[i]) ? 0 : 1;

    return true;
}

auto Disjunctive::define_proof_model(ProofModel & model) -> void
{
    // Declarative pairwise OPB encoding:
    //   for each unordered pair (i, j) of participating tasks:
    //     before_{i,j} <-> starts[i] + lengths[i] <= starts[j]
    //     before_{j,i} <-> starts[j] + lengths[j] <= starts[i]
    //   then one clause per pair:
    //     before_{i,j} v before_{j,i}
    //
    // This is the only thing that goes into the OPB: the constraint's
    // declarative meaning, free of time-table or other propagator-specific
    // scaffolding. The bridge to active/before/after-at-time flags is
    // introduced in install_propagators's initialiser, scoped to the proof.
    //
    // Line numbers of both reification halves of each before flag, and of
    // each pairwise clause, are stored so the propagator can pol them into
    // bridge-derived at-most-one lemmas during justifications.
    // For a task with a variable duration, the "after" bridge flag reifies on a
    // proof-only end = s + l (a single variable keeps the pin RUP-friendly).
    // The end proxy end_i = start_i + length_i (only for variable durations) is a
    // proof-only variable with NO OPB encoding: cake has no such variable (it folds
    // start + length directly into the before-link), so there is nothing to match.
    // Its definition is introduced INSIDE the proof, by the install_initialiser
    // below, via ProofLogger::introduce_bits_of --- a conservative extension rather
    // than a model axiom, which is what makes the variable-duration proof
    // chain-portable. end_ge / end_le are captured there, not here.
    _end.assign(_starts.size(), nullopt);
    for (auto i : _active_tasks)
        if (! is_constant_variable(_lengths[i]))
            _end[i] = model.create_proof_only_integer_variable_in_proof(0_i, _per_task_t_hi[i] + 1_i, "disjend");

    // Non-strict mode: a "duration <= 0" escape flag per variable-duration
    // task, added as a disjunct to the separation clause below (a zero-length
    // task does not constrain). nullopt otherwise.
    _zero.assign(_starts.size(), nullopt);
    for (auto i : _active_tasks)
        if (_zero_escape[i])
            // cake_pb_cp names the zero-duration escape x[id][i][zw].
            _zero[i] = model.create_proof_flag_fully_reifying(
                _constraint_id, vector<long long>{static_cast<long long>(i)}, "zw", WPBSum{} + 1_i * _lengths[i] <= 0_i);

    // before_{i,j} <-> s_i + l_i <= s_j. For a constant duration this folds to
    // s_i - s_j <= -l (byte-identical to the constant-only implementation); for
    // a variable duration the length term stays on the left.
    auto emit_before = [&](size_t i, size_t j) -> BeforeFlagData {
        // cake_pb_cp names the "task i finishes before task j starts" flag
        // x[id][i_j][bf]; match it for verified-encoding compatibility.
        auto flag = model.create_proof_flag(_constraint_id, vector<long long>{static_cast<long long>(i), static_cast<long long>(j)}, "bf");
        auto ineq = is_constant_variable(_lengths[i]) ? (WPBSum{} + 1_i * _starts[i] + -1_i * _starts[j] <= -_length_vals[i])
                                                      : (WPBSum{} + 1_i * _starts[i] + 1_i * _lengths[i] + -1_i * _starts[j] <= 0_i);
        auto [fwd, rev] = model.add_two_way_reified_constraint(ineq, flag);
        return BeforeFlagData{flag, fwd, rev};
    };
    for (size_t a = 0; a < _active_tasks.size(); ++a) {
        auto i = _active_tasks[a];
        for (size_t b = a + 1; b < _active_tasks.size(); ++b) {
            auto j = _active_tasks[b];
            auto data_ij = emit_before(i, j);
            auto data_ji = emit_before(j, i);
            // A zero-length task escapes the separation clause (non-strict).
            auto clause_sum = WPBSum{} + 1_i * data_ij.flag + 1_i * data_ji.flag;
            for (auto r : {i, j})
                if (_zero[r])
                    clause_sum += 1_i * *_zero[r];
            // cake_pb_cp labels the separation clause @c[id][<i>_<j>sepal1].
            auto clause =
                model.add_labelled_constraint(_constraint_id, std::to_string(i) + "_" + std::to_string(j) + "sepal1", move(clause_sum) >= 1_i);
            _before_flags.emplace(std::make_pair(i, j), data_ij);
            _before_flags.emplace(std::make_pair(j, i), data_ji);
            _clause_lines.emplace(std::make_pair(i, j), clause);
        }
    }
}

namespace
{
    // Per-(task, t) bridge flags introduced by install_propagators's
    // initialiser at search root. These connect the declarative pairwise
    // OPB encoding to the time-table reasoning the propagator uses, but
    // live entirely in the proof database (not in the OPB) so the OPB
    // stays the declarative truth.
    struct BridgeFlags
    {
        ProofFlag before; // before_{i,t} <-> starts[i] <= t
        ProofLine before_fwd;
        ProofLine before_rev;
        ProofFlag after; // after_{i,t} <-> starts[i] + lengths[i] >= t + 1
        ProofLine after_fwd;
        ProofLine after_rev;
        ProofFlag active; // active_{i,t} <-> before_{i,t} ^ after_{i,t}
        ProofLine active_fwd;
        ProofLine active_rev;
    };
    using BridgeMap = map<pair<size_t, Integer>, BridgeFlags>;
}

auto Disjunctive::install_propagators(Propagators & propagators) -> void
{
    // The OPB stays declarative (just the pairwise clauses emitted in
    // define_proof_model). The bridge to time-indexed before/after/active
    // flags is propagator scaffolding, created here in the proof. An
    // initialiser runs once at search root and pre-emits all bridge flags
    // for every (task, t) in each task's possible-active window, at
    // ProofLevel::Top so the flags survive across the entire search. The
    // propagator looks them up by (task, t) during justifications.
    //
    // Creating flags only at Top + once per (task, t) avoids the
    // exponential-memory pitfall of lazy mid-proof flag creation: Glasgow
    // currently has no flag-deletion API, so every fresh flag accumulates
    // in NamesAndIDsTracker. Eager root-time emission bounds the total to
    // O(n * horizon) flags per Disjunctive instance.
    auto bridge = make_shared<BridgeMap>();

    // Lazily-introduced end_i = s_i + l_i definitions: {end_ge, end_le} per task,
    // filled the first time a variable-duration task's after reasoning fires (see
    // ensure_end in the propagator). Shared so the cache survives across calls.
    auto end_lines = make_shared<vector<optional<pair<ProofLine, ProofLine>>>>(_starts.size());

    propagators.install_initialiser([starts = _starts, lengths = _length_vals, length_vars = _lengths, length_ub = _length_ub, ends = _end, end_lines,
                                        active_tasks = _active_tasks, per_task_t_lo = _per_task_t_lo, per_task_t_hi = _per_task_t_hi,
                                        bridge](State &, auto &, ProofLogger * const logger) -> void {
        if (! logger || logger->get_assertion_level() > AssertionLevel::Off)
            return;
        // Introduce each variable-duration end_i = s_i + l_i as a conservative
        // extension FIRST --- before the after-flag definitions below reify on
        // end_i (which references its bits), so that the bits are still fresh
        // for introduce_bits_of's redundancy witnesses. Captured for the
        // propagator's materialise_end / before-flag pol.
        for (auto i : active_tasks)
            if (ends[i].has_value())
                (*end_lines)[i] = logger->introduce_bits_of(WPBSum{} + 1_i * starts[i] + 1_i * length_vars[i], *ends[i], ProofLevel::Top);
        for (auto i : active_tasks) {
            if (length_ub[i] == 0_i)
                continue;
            for (Integer t = per_task_t_lo[i]; t <= per_task_t_hi[i]; ++t) {
                auto [B, B_fwd, B_rev] = logger->create_proof_flag_reifying(WPBSum{} + 1_i * starts[i] <= t, "djbef", ProofLevel::Top);
                // after_{i,t} <-> s_i + l_i >= t+1. Constant duration: the
                // single-variable s_i >= t-l+1. Variable duration: the
                // single-variable end_i >= t+1 (end_i = s_i + l_i).
                auto [F, F_fwd, F_rev] = ends[i].has_value()
                    ? logger->create_proof_flag_reifying(WPBSum{} + 1_i * *ends[i] >= t + 1_i, "djaft", ProofLevel::Top)
                    : logger->create_proof_flag_reifying(WPBSum{} + 1_i * starts[i] >= t - lengths[i] + 1_i, "djaft", ProofLevel::Top);
                auto [A, A_fwd, A_rev] = logger->create_proof_flag_reifying(WPBSum{} + 1_i * B + 1_i * F >= 2_i, "djact", ProofLevel::Top);
                bridge->emplace(make_pair(i, t), BridgeFlags{B, B_fwd, B_rev, F, F_fwd, F_rev, A, A_fwd, A_rev});
            }
        }
    });

    Triggers triggers;
    for (auto i : _active_tasks) {
        triggers.on_bounds.emplace_back(_starts[i]);
        // A rise in a task's minimum duration extends its mandatory part, so
        // re-fire on variable-duration bound changes too.
        if (! is_constant_variable(_lengths[i]))
            triggers.on_bounds.emplace_back(_lengths[i]);
    }

    propagators.install(
        constraint_id(),
        [starts = move(_starts), lengths = move(_length_vals), length_vars = move(_lengths), ends = move(_end), end_lines, zero = move(_zero),
            strict = _strict, active_tasks = move(_active_tasks), before_flags = move(_before_flags), clause_lines = move(_clause_lines),
            owner = constraint_id(), bridge](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // Current guaranteed (min) and possible (max) duration of task i:
            // for a constant duration both are the value; for a variable
            // duration they are the live lower / upper bounds.
            auto is_var_len = [&](size_t i) -> bool { return ! is_constant_variable(length_vars[i]); };
            auto min_len = [&](size_t i) -> Integer { return is_var_len(i) ? state.lower_bound(length_vars[i]) : lengths[i]; };
            auto max_len = [&](size_t i) -> Integer { return is_var_len(i) ? state.upper_bound(length_vars[i]) : lengths[i]; };

            // The pairwise proof vocabulary. Everything the propagator infers
            // is justified through the encoded before-flags: a pol over a
            // flag's [r] row (flag -> s_a + l_a <= s_b) plus one bound-literal
            // definition row per operand cancels the integer terms exactly,
            // leaving a clause over the flag's negation and the residual
            // order literals, which the closing reason-wrapped RUPs then
            // unit-propagate. The pol is load-bearing: bare RUP cannot
            // transfer a bound row's cap into the reification row's slack
            // when the overlap margin is smaller than the residual
            // bit-encoding range. See dev_docs/disjunctive-proof-logging.md.
            //
            // cond_a / cond_b are the bound literals cited for s_a and s_b
            // (nullopt for a constant start, whose value is already folded
            // into the flag's row); a variable duration l_a additionally
            // cites its current lower bound (the reason covers it).
            auto emit_before_pol = [&](size_t a, size_t b, const optional<IntegerVariableCondition> & cond_a,
                                       const optional<IntegerVariableCondition> & cond_b) -> void {
                auto & tracker = logger->names_and_ids_tracker();
                PolBuilder pol;
                pol.add(before_flags.at(make_pair(a, b)).forward_line);
                if (cond_a)
                    pol.add_for_literal(tracker, *cond_a);
                if (is_var_len(a))
                    pol.add_for_literal(tracker, length_vars[a] >= state.lower_bound(length_vars[a]));
                if (cond_b)
                    pol.add_for_literal(tracker, *cond_b);
                pol.saturate().emit(*logger, ProofLevel::Temporary);
            };

            // The current-bound literals on a task's start, or nullopt for a
            // constant start (a constant has no defining literal to cite).
            auto start_lb_lit = [&](size_t i) -> optional<IntegerVariableCondition> {
                if (is_constant_variable(starts[i]))
                    return nullopt;
                return starts[i] >= state.lower_bound(starts[i]);
            };
            auto start_ub_lit = [&](size_t i) -> optional<IntegerVariableCondition> {
                if (is_constant_variable(starts[i]))
                    return nullopt;
                return starts[i] < state.upper_bound(starts[i]) + 1_i;
            };

            // Non-strict mode: every task involved in an inference has a
            // positive guaranteed duration (it contributes a mandatory part
            // or footprint), so its zero-length escape flag is false. Pin
            // those flags false (RUP under reason, from the duration's lower
            // bound) so the separation clauses reduce to their before-flag
            // disjunctions. No-op in strict mode / for always-positive
            // durations.
            auto pin_escapes = [&](const ReasonLiterals & reason, const vector<size_t> & tasks) -> void {
                for (auto r : tasks)
                    if (zero[r])
                        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * *zero[r] <= 0_i, ProofLevel::Temporary);
            };

            // Time-table consistency, specialised to heights = 1 and
            // capacity = 1. Mandatory part of task i is [lst_i, eet_i)
            // where lst_i = ub(s_i) and eet_i = lb(s_i) + l_i: the slice it
            // must occupy regardless of where it starts. Two tasks whose
            // mandatory parts overlap is infeasible, and any per-task start
            // that would force a mandatory-part collision is excluded.
            //
            // Zero-length tasks contribute nothing to the profile but in
            // strict mode are still constrained: a zero-length task's
            // point may not sit strictly inside any other task's open
            // active interval. The TT pass misses that case; we catch it
            // below with an all-fixed pairwise check.
            //
            bool any = false;
            Integer t_lo = 0_i, t_hi = -1_i;
            for (auto i : active_tasks) {
                if (max_len(i) == 0_i)
                    continue;
                auto [s_lo, s_hi] = state.bounds(starts[i]);
                auto lo = s_lo, hi = s_hi + max_len(i) - 1_i;
                if (! any || lo < t_lo)
                    t_lo = lo;
                if (! any || hi > t_hi)
                    t_hi = hi;
                any = true;
            }

            if (any) {
                auto range = (t_hi - t_lo + 1_i).raw_value;
                vector<int> mand_load(range, 0);

                for (auto i : active_tasks) {
                    if (min_len(i) == 0_i)
                        continue;
                    auto lst = state.upper_bound(starts[i]);
                    auto eet = state.lower_bound(starts[i]) + min_len(i);
                    if (lst < eet)
                        for (Integer t = lst; t < eet; ++t)
                            ++mand_load[(t - t_lo).raw_value];
                }

                for (auto idx = 0; idx < range; ++idx)
                    if (mand_load[idx] > 1) {
                        auto violating_t = t_lo + Integer{idx};
                        // Find the first two tasks whose mandatory parts cover
                        // violating_t. With h=1, c=1, two is enough: any one
                        // pairwise atmost-one + their active=1 lines pol to a
                        // contradiction.
                        size_t pi = 0, pj = 0;
                        bool got_first = false, got_second = false;
                        for (auto i : active_tasks) {
                            if (min_len(i) == 0_i)
                                continue;
                            auto lst = state.upper_bound(starts[i]);
                            auto eet = state.lower_bound(starts[i]) + min_len(i);
                            if (lst < eet && violating_t >= lst && violating_t < eet) {
                                if (! got_first) {
                                    pi = i;
                                    got_first = true;
                                }
                                else {
                                    pj = i;
                                    got_second = true;
                                    break;
                                }
                            }
                        }
                        if (! got_second)
                            throw UnexpectedException{"Disjunctive: mand_load > 1 without two contributing tasks"};

                        auto justify = [&, pi, pj](const ReasonLiterals & reason) -> void {
                            pin_escapes(reason, {pi, pj});
                            // The mandatory parts overlap at violating_t, so
                            // neither task can finish before the other starts:
                            // each before flag's [r] row plus the mandatory
                            // bounds (lb of the finisher's start and duration,
                            // ub of the other's start) is infeasible, so one
                            // pol per flag forces it false under the reason,
                            // and the separation clause unit-fails in the
                            // framework's closing reason-wrapped RUP.
                            emit_before_pol(pi, pj, start_lb_lit(pi), start_ub_lit(pj));
                            emit_before_pol(pj, pi, start_lb_lit(pj), start_ub_lit(pi));
                        };

                        // The pols cite lb(l) for variable-length tasks, so
                        // those durations must be part of the reason.
                        auto reason_vars = starts;
                        if (is_var_len(pi))
                            reason_vars.push_back(length_vars[pi]);
                        if (is_var_len(pj))
                            reason_vars.push_back(length_vars[pj]);
                        inference.contradiction(
                            logger, JustifyExplicitly{justify, ThenRUP::Yes, hints::Disjunctive{owner}}, generic_reason(reason_vars));
                        return PropagatorState::DisableUntilBacktrack;
                    }

                // Variable durations join the reason for the push proofs (the
                // pols and mandatory parts read lb(l)). For a constant-only
                // instance this is just the starts, leaving the proof
                // byte-identical.
                auto push_reason_vars = starts;
                for (auto i : active_tasks)
                    if (is_var_len(i))
                        push_reason_vars.push_back(length_vars[i]);

                // One step of an lb/ub-push chain: a single blocking task and
                // the start bound the pair dichotomy advances to (the
                // blocker's mandatory end for an lb-push, its latest start
                // minus lb(l_j) for a ub-push). One step per BLOCKER, however
                // long the blocker: with the running bound established, j's
                // next lb(l_j) slots reach into the blocker's mandatory part,
                // so "j finishes before k starts" is impossible and the
                // encoded pairwise clause forces "k finishes before j starts",
                // which advances the bound in one dichotomy.
                struct ChainStep
                {
                    size_t blocker;
                    Integer target;
                };

                // Per-step proof emitter. `bound` is the running bound the
                // step starts from (established by the reason for the first
                // step, by the previous step's deposit after), `final` says
                // whether the framework's closing RUP concludes the target
                // instead of an explicit intermediate deposit.
                auto emit_lb_chain_step = [&](size_t j, size_t k, Integer bound, Integer target, bool final, const ReasonLiterals & reason) -> void {
                    // Left branch: j finishing before k contradicts the
                    // running bound -- s_j >= bound plus lb(l_j) reaches past
                    // ub(s_k), forcing bf_{j,k} false.
                    emit_before_pol(j, k, starts[j] >= bound, start_ub_lit(k));
                    // Right branch: k finishing before j puts s_j at k's
                    // mandatory end or later, folded onto the target order
                    // literal's definition row: bf_{k,j} -> s_j >= target.
                    emit_before_pol(k, j, start_lb_lit(k), starts[j] < target);
                    // Intermediate steps deposit the advanced bound under the
                    // reason so the next step's left branch unit-propagates
                    // from it; the final target is exactly the inferred
                    // bound, which the framework's closing RUP concludes.
                    if (! final)
                        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (starts[j] >= target) >= 1_i, ProofLevel::Temporary);
                };
                auto emit_ub_chain_step = [&](size_t j, size_t k, Integer bound, Integer target, bool final, const ReasonLiterals & reason) -> void {
                    // Mirror of the lb step. Left branch: k finishing before j
                    // is impossible under the running bound -- s_j would be at
                    // k's mandatory end or later, past bound.
                    emit_before_pol(k, j, start_lb_lit(k), starts[j] < bound + 1_i);
                    // Right branch: j finishing before k caps s_j at k's
                    // latest start minus lb(l_j), folded onto the target order
                    // literal's definition row: bf_{j,k} -> s_j <= target.
                    emit_before_pol(j, k, starts[j] >= target + 1_i, start_ub_lit(k));
                    if (! final)
                        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (starts[j] < target + 1_i) >= 1_i, ProofLevel::Temporary);
                };

                for (auto j : active_tasks) {
                    if (min_len(j) == 0_i)
                        continue;
                    auto [cur_lb, cur_ub] = state.bounds(starts[j]);
                    if (cur_lb == cur_ub)
                        continue;

                    auto lst_j = cur_ub, eet_j = cur_lb + min_len(j);
                    auto fits_at = [&](Integer s) -> bool {
                        for (Integer t = s; t < s + min_len(j); ++t) {
                            auto load = mand_load[(t - t_lo).raw_value];
                            if (lst_j < eet_j && t >= lst_j && t < eet_j)
                                --load;
                            if (load >= 1)
                                return false;
                        }
                        return true;
                    };

                    // A blocker for a chain step at running bound `bound`: a
                    // task (other than j) whose mandatory part intersects the
                    // window [bound, bound + lb(l_j)). Every non-fitting start
                    // is blocked, so while the chain has ground to cover one
                    // exists; `better` picks the most useful of two candidate
                    // mandatory parts (deepest end for an lb-push, leftmost
                    // start for a ub-push). Reads current bounds, which may be
                    // tighter than the profile (mandatory parts only grow
                    // within a pass), hence the clipping in the chain loops
                    // below.
                    auto find_blocker = [&](size_t j, Integer bound, const auto & better) -> pair<size_t, pair<Integer, Integer>> {
                        optional<size_t> blocker;
                        pair<Integer, Integer> best_mand{0_i, 0_i};
                        for (auto k : active_tasks) {
                            if (k == j || min_len(k) == 0_i)
                                continue;
                            auto lst_k = state.upper_bound(starts[k]);
                            auto eet_k = state.lower_bound(starts[k]) + min_len(k);
                            if (lst_k < eet_k && lst_k < bound + min_len(j) && eet_k > bound &&
                                (! blocker || better(pair{lst_k, eet_k}, best_mand))) {
                                blocker = k;
                                best_mand = pair{lst_k, eet_k};
                            }
                        }
                        if (! blocker)
                            throw UnexpectedException{"Disjunctive: no blocker for a push chain step"};
                        return {*blocker, best_mand};
                    };

                    // lb-push: scan upward to find the smallest fitting start,
                    // then justify with one dichotomy step per blocker, each
                    // advancing the running bound to the blocker's mandatory
                    // end -- clipped to new_lb, both because the profile may
                    // be staler than the bounds the steps cite and so the
                    // final step lands exactly on the inferred bound.
                    auto new_lb = cur_lb;
                    while (new_lb <= cur_ub && ! fits_at(new_lb))
                        ++new_lb;
                    if (new_lb > cur_lb) {
                        vector<ChainStep> chain;
                        if (logger) {
                            Integer bound = cur_lb;
                            while (bound < new_lb) {
                                auto [k, mand] = find_blocker(j, bound, [](const auto & a, const auto & b) { return a.second > b.second; });
                                chain.push_back(ChainStep{k, min(mand.second, new_lb)});
                                bound = chain.back().target;
                            }
                        }

                        auto justify = [&, j, cur_lb, chain](const ReasonLiterals & reason) -> void {
                            vector<size_t> involved{j};
                            for (const auto & step : chain)
                                involved.push_back(step.blocker);
                            pin_escapes(reason, involved);
                            Integer bound = cur_lb;
                            for (size_t step = 0; step < chain.size(); ++step) {
                                emit_lb_chain_step(j, chain[step].blocker, bound, chain[step].target, step + 1 == chain.size(), reason);
                                bound = chain[step].target;
                            }
                        };

                        inference.infer_greater_than_or_equal(logger, starts[j], new_lb,
                            JustifyExplicitly{justify, ThenRUP::Yes, hints::Disjunctive{owner}}, generic_reason(push_reason_vars));
                    }

                    // ub-push: mirror of lb-push, scanning downward, each step
                    // dropping the running bound to the blocker's latest start
                    // minus lb(l_j) (the last start from which j finishes by
                    // the time the blocker must have started), clipped to
                    // new_ub.
                    auto new_ub = cur_ub;
                    while (new_ub >= cur_lb && ! fits_at(new_ub))
                        --new_ub;
                    if (new_ub < cur_ub) {
                        vector<ChainStep> chain;
                        if (logger) {
                            Integer bound = cur_ub;
                            while (bound > new_ub) {
                                auto [k, mand] = find_blocker(j, bound, [](const auto & a, const auto & b) { return a.first < b.first; });
                                chain.push_back(ChainStep{k, max(mand.first - min_len(j), new_ub)});
                                bound = chain.back().target;
                            }
                        }

                        auto justify = [&, j, cur_ub, chain](const ReasonLiterals & reason) -> void {
                            vector<size_t> involved{j};
                            for (const auto & step : chain)
                                involved.push_back(step.blocker);
                            pin_escapes(reason, involved);
                            Integer bound = cur_ub;
                            for (size_t step = 0; step < chain.size(); ++step) {
                                emit_ub_chain_step(j, chain[step].blocker, bound, chain[step].target, step + 1 == chain.size(), reason);
                                bound = chain[step].target;
                            }
                        };

                        inference.infer_less_than(logger, starts[j], new_ub + 1_i,
                            JustifyExplicitly{justify, ThenRUP::Yes, hints::Disjunctive{owner}}, generic_reason(push_reason_vars));
                    }
                }
            }

            // Strict-mode zero-length tasks: check that no zero-length task
            // (constant 0, or a variable duration currently fixed to 0) with a
            // fixed start sits strictly inside another task's open active
            // interval, where that task has a fixed start and a fixed positive
            // duration. Non-strict mode skips this entirely: a zero-length task
            // floats freely (and the separation clause's zero escape allows it).
            //
            // The proof is JustifyUsingRUP: at this all-fixed leaf the
            // declarative pairwise encoding alone is enough. With s_z, s_k (and
            // any variable durations) fixed at vz, vk, l_k satisfying
            // vk < vz < vk + l_k, before_{z,k} = (vz <= vk) UPs to 0 and
            // before_{k,z} = (vk + l_k <= vz) UPs to 0, contradicting the
            // encoded clause before_{z,k} + before_{k,z} >= 1.
            for (auto z : active_tasks) {
                if (! strict)
                    break;
                if (max_len(z) > 0_i)
                    continue;
                if (! state.has_single_value(starts[z]))
                    continue;
                auto vz = state.lower_bound(starts[z]);
                for (auto k : active_tasks) {
                    // k must have a fixed, positive duration.
                    if (k == z || min_len(k) != max_len(k) || min_len(k) == 0_i)
                        continue;
                    if (! state.has_single_value(starts[k]))
                        continue;
                    auto vk = state.lower_bound(starts[k]);
                    if (vk < vz && vz < vk + min_len(k)) {
                        auto reason_vars = starts;
                        if (is_var_len(z))
                            reason_vars.push_back(length_vars[z]);
                        if (is_var_len(k))
                            reason_vars.push_back(length_vars[k]);
                        inference.contradiction(logger, JustifyUsingRUP{hints::Disjunctive{owner}}, generic_reason(reason_vars));
                        return PropagatorState::DisableUntilBacktrack;
                    }
                }
            }

            return PropagatorState::Enable;
        },
        triggers);
}

auto Disjunctive::constraint_type() const -> std::string
{
    return _strict ? "disjunctive_strict" : "disjunctive";
}

auto Disjunctive::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    vector<SExpr> starts, lengths;
    for (const auto & v : _starts)
        starts.push_back(tracker.s_expr_term_of(v));
    for (const auto & l : _lengths)
        lengths.push_back(is_constant_variable(l) ? SExpr::atom(const_value_of(l).to_string()) : tracker.s_expr_term_of(l));
    return SExpr::list(
        {SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(std::move(starts)), SExpr::list(std::move(lengths))});
}
