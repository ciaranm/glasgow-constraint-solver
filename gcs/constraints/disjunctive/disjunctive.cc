#include <gcs/constraints/disjunctive/disjunctive.hh>
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

Disjunctive::Disjunctive(vector<IntegerVariableID> starts, vector<IntegerVariableID> lengths, bool strict) :
    _starts(move(starts)),
    _lengths(move(lengths)),
    _strict(strict)
{
    if (_starts.size() != _lengths.size())
        throw InvalidProblemDefinitionException{"Disjunctive: starts and lengths must have the same size"};
    // Constant durations are checked here; variable durations are checked
    // against their root lower bound in prepare().
    for (const auto & l : _lengths)
        if (is_constant_variable(l) && const_value_of(l) < 0_i)
            throw InvalidProblemDefinitionException{"Disjunctive: lengths must be non-negative"};
}

Disjunctive::Disjunctive(vector<IntegerVariableID> starts, vector<Integer> lengths, bool strict) :
    Disjunctive(move(starts), as_constant_var_ids(lengths), strict)
{
}

auto Disjunctive::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Disjunctive>(_starts, _lengths, _strict);
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

    // Non-strict mode: note which active tasks' durations can be 0, so
    // define_proof_model can add a zero-length escape to the separation clause.
    // The propagator already ignores zero-mandatory tasks via lb(l).
    _can_be_zero.assign(n, 0);
    if (! _strict)
        for (auto i : _active_tasks)
            _can_be_zero[i] = (! is_constant_variable(_lengths[i]) &&
                                  initial_state.lower_bound(_lengths[i]) == 0_i)
                ? 1
                : 0;

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
    // Capture both definition directions: _end_ge materialises end's bound and
    // _end_le cancels end back to s + l in the before-flag pol.
    _end.assign(_starts.size(), nullopt);
    _end_ge.assign(_starts.size(), nullopt);
    _end_le.assign(_starts.size(), nullopt);
    for (auto i : _active_tasks) {
        if (is_constant_variable(_lengths[i]))
            continue;
        auto end = model.create_proof_only_integer_variable(
            0_i, _per_task_t_hi[i] + 1_i, "disjend", IntegerVariableProofRepresentation::Bits);
        _end_ge[i] = model.add_constraint("Disjunctive", "end >= s + l",
            WPBSum{} + 1_i * end + -1_i * _starts[i] + -1_i * _lengths[i] >= 0_i);
        _end_le[i] = model.add_constraint("Disjunctive", "end <= s + l",
            WPBSum{} + 1_i * end + -1_i * _starts[i] + -1_i * _lengths[i] <= 0_i);
        _end[i] = end;
    }

    // Non-strict mode: a "duration <= 0" escape flag per can-be-zero task, added
    // as a disjunct to the separation clause below (a zero-length task does not
    // constrain). nullopt otherwise.
    _zero.assign(_starts.size(), nullopt);
    for (auto i : _active_tasks)
        if (_can_be_zero[i])
            // cake_pb_cp names the zero-duration escape x[id][i][zw].
            _zero[i] = model.create_proof_flag_fully_reifying(
                _constraint_id, vector<long long>{static_cast<long long>(i)}, "zw",
                WPBSum{} + 1_i * _lengths[i] <= 0_i);

    // before_{i,j} <-> s_i + l_i <= s_j. For a constant duration this folds to
    // s_i - s_j <= -l (byte-identical to the constant-only implementation); for
    // a variable duration the length term stays on the left.
    auto emit_before = [&](size_t i, size_t j) -> BeforeFlagData {
        // cake_pb_cp names the "task i finishes before task j starts" flag
        // x[id][i_j][bf]; match it for verified-encoding compatibility.
        auto flag = model.create_proof_flag(_constraint_id,
            vector<long long>{static_cast<long long>(i), static_cast<long long>(j)}, "bf");
        auto ineq = is_constant_variable(_lengths[i])
            ? (WPBSum{} + 1_i * _starts[i] + -1_i * _starts[j] <= -_length_vals[i])
            : (WPBSum{} + 1_i * _starts[i] + 1_i * _lengths[i] + -1_i * _starts[j] <= 0_i);
        auto [fwd, rev] = model.add_two_way_reified_constraint(
            "Disjunctive", "first task finishes before second starts", ineq, flag);
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
            auto clause = model.add_constraint("Disjunctive", "one task must finish first",
                move(clause_sum) >= 1_i);
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

    propagators.install_initialiser(
        [starts = _starts, lengths = _length_vals, length_ub = _length_ub, ends = _end,
            active_tasks = _active_tasks, per_task_t_lo = _per_task_t_lo,
            per_task_t_hi = _per_task_t_hi, bridge](State &, auto &, ProofLogger * const logger) -> void {
            if (! logger || logger->get_assertion_level() > AssertionLevel::Off)
                return;
            for (auto i : active_tasks) {
                if (length_ub[i] == 0_i)
                    continue;
                for (Integer t = per_task_t_lo[i]; t <= per_task_t_hi[i]; ++t) {
                    auto [B, B_fwd, B_rev] = logger->create_proof_flag_reifying(
                        WPBSum{} + 1_i * starts[i] <= t,
                        "djbef", ProofLevel::Top);
                    // after_{i,t} <-> s_i + l_i >= t+1. Constant duration: the
                    // single-variable s_i >= t-l+1. Variable duration: the
                    // single-variable end_i >= t+1 (end_i = s_i + l_i).
                    auto [F, F_fwd, F_rev] = ends[i].has_value()
                        ? logger->create_proof_flag_reifying(
                              WPBSum{} + 1_i * *ends[i] >= t + 1_i, "djaft", ProofLevel::Top)
                        : logger->create_proof_flag_reifying(
                              WPBSum{} + 1_i * starts[i] >= t - lengths[i] + 1_i, "djaft", ProofLevel::Top);
                    auto [A, A_fwd, A_rev] = logger->create_proof_flag_reifying(
                        WPBSum{} + 1_i * B + 1_i * F >= 2_i,
                        "djact", ProofLevel::Top);
                    bridge->emplace(make_pair(i, t),
                        BridgeFlags{B, B_fwd, B_rev, F, F_fwd, F_rev, A, A_fwd, A_rev});
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
        [starts = move(_starts), lengths = move(_length_vals), length_vars = move(_lengths),
            end_ge = move(_end_ge), end_le = move(_end_le), zero = move(_zero), strict = _strict,
            active_tasks = move(_active_tasks), before_flags = move(_before_flags),
            clause_lines = move(_clause_lines), bridge](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // Current guaranteed (min) and possible (max) duration of task i:
            // for a constant duration both are the value; for a variable
            // duration they are the live lower / upper bounds.
            auto is_var_len = [&](size_t i) -> bool { return ! is_constant_variable(length_vars[i]); };
            auto min_len = [&](size_t i) -> Integer {
                return is_var_len(i) ? state.lower_bound(length_vars[i]) : lengths[i];
            };
            auto max_len = [&](size_t i) -> Integer {
                return is_var_len(i) ? state.upper_bound(length_vars[i]) : lengths[i];
            };

            // For a variable-duration task, materialise end_i >= s_lo + lb(l_i)
            // via a pol over the captured end >= s+l line plus the start and
            // length order-literals, so the after-flag RUP closes single-variable
            // in end. A constant start is folded into end_ge's RHS and so
            // contributes no literal (a constant has no pol-defining literal).
            // No-op for a constant duration (after is already single-variable).
            auto materialise_end = [&](size_t i, Integer s_lo) -> void {
                if (! is_var_len(i))
                    return;
                PolBuilder pb;
                pb.add(*end_ge[i]);
                if (! is_constant_variable(starts[i]))
                    pb.add_for_literal(logger->names_and_ids_tracker(), starts[i] >= s_lo);
                pb.add_for_literal(logger->names_and_ids_tracker(),
                    length_vars[i] >= state.lower_bound(length_vars[i]));
                pb.emit(*logger, ProofLevel::Temporary);
            };

            // Non-strict mode: every task involved in a contradiction / push has
            // a positive guaranteed duration (it contributes a mandatory part or
            // footprint), so its zero-length escape flag is false. Pin those
            // flags false (RUP under reason) and add them to a clause pol so the
            // separation clause reduces to its before-flag disjunction. No-op in
            // strict mode / for always-positive durations.
            auto add_escape_pins = [&](PolBuilder & pol, const ReasonLiterals & reason, size_t i, size_t j) {
                for (auto r : {i, j})
                    if (zero[r])
                        pol.add(logger->emit_rup_proof_line_under_reason(reason,
                            WPBSum{} + 1_i * *zero[r] <= 0_i, ProofLevel::Temporary));
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
            // Contradiction justifications are proof-logged via the bridge.
            // lb/ub-push justifications are still stubbed with
            // AssertRatherThanJustifying; they get the chain-step treatment
            // in stage 3b/3c.
            bool any = false;
            Integer t_lo = 0_i, t_hi = -1_i;
            for (auto i : active_tasks) {
                if (max_len(i) == 0_i)
                    continue;
                auto [s_lo, s_hi] = state.bounds(starts[i]);
                auto lo = s_lo, hi = s_hi + max_len(i) - 1_i;
                if (! any || lo < t_lo) t_lo = lo;
                if (! any || hi > t_hi) t_hi = hi;
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
                            throw UnexpectedException{
                                "Disjunctive: mand_load > 1 without two contributing tasks"};

                        auto justify = [&, violating_t, pi, pj](const ReasonLiterals & reason) -> void {
                            auto & bf_i = bridge->at(make_pair(pi, violating_t));
                            auto & bf_j = bridge->at(make_pair(pj, violating_t));

                            // Pin active_{r,vt} = 1 under the bounds reason.
                            // Cumulative-style chain: before, then after, then
                            // active — VeriPB UP can't chase the AND-gate of
                            // active's reverse half in one step. For a variable
                            // duration the after flag reifies on end = s + l, so
                            // materialise end >= lb(s) + lb(l) first (the
                            // end-proxy technique) so the after RUP closes
                            // single-variable in end.
                            auto pin = [&](const BridgeFlags & bf, size_t r) -> ProofLine {
                                logger->emit_rup_proof_line_under_reason(reason,
                                    WPBSum{} + 1_i * bf.before >= 1_i, ProofLevel::Temporary);
                                // A mandatory task has s_r + l_r >= lb(s_r) + lb(l_r) > vt.
                                materialise_end(r, state.lower_bound(starts[r]));
                                logger->emit_rup_proof_line_under_reason(reason,
                                    WPBSum{} + 1_i * bf.after >= 1_i, ProofLevel::Temporary);
                                return logger->emit_rup_proof_line_under_reason(reason,
                                    WPBSum{} + 1_i * bf.active >= 1_i, ProofLevel::Temporary);
                            };
                            auto A_i_line = pin(bf_i, pi);
                            auto A_j_line = pin(bf_j, pj);

                            // Pairwise atmost-one over {A_i, A_j} via
                            // recover_am1. The pair_ne callback derives one
                            // such line via a three-step pol that lifts the
                            // encoded pairwise clause + before-flag forward
                            // reifs into a constraint over the bridge flags.
                            // Each step's integer-variable terms cancel
                            // exactly: s_i and s_j contributions sum to 0
                            // (e.g. (s_j - s_i) from E_ij_fwd, +s_i from
                            // F_i_fwd, -s_j from B_j_fwd), leaving a clean
                            // flag-only constraint after saturation.
                            map<ProofFlag, size_t> flag_to_task;
                            flag_to_task.emplace(bf_i.active, pi);
                            flag_to_task.emplace(bf_j.active, pj);

                            auto pair_ne = [&](const ProofFlag & a, const ProofFlag & b) -> ProofLine {
                                auto ti = flag_to_task.at(a);
                                auto tj = flag_to_task.at(b);
                                auto & bfi = bridge->at(make_pair(ti, violating_t));
                                auto & bfj = bridge->at(make_pair(tj, violating_t));
                                auto & e_ij = before_flags.at(make_pair(ti, tj));
                                auto & e_ji = before_flags.at(make_pair(tj, ti));
                                auto clause_line = clause_lines.at(
                                    make_pair(min(ti, tj), max(ti, tj)));

                                // L1: E_ij_fwd + F_i_fwd + B_j_fwd, plus end_le[i]
                                // for a variable duration (cancels end back to
                                // s_i + l_i), then saturate. The integer terms
                                // cancel to 0, RHS = 1, giving ¬E_ij + ¬F_i +
                                // ¬B_j >= 1. L2 is symmetric, swapping i and j.
                                auto Lpol = [&](ProofLine before_line, const BridgeFlags & aft,
                                                const BridgeFlags & bef, const optional<ProofLine> & aft_end_le) -> ProofLine {
                                    PolBuilder pol;
                                    pol.add(before_line).add(aft.after_fwd).add(bef.before_fwd);
                                    if (aft_end_le)
                                        pol.add(*aft_end_le);
                                    return pol.saturate().emit(*logger, ProofLevel::Temporary);
                                };
                                auto L1 = Lpol(e_ij.forward_line, bfi, bfj, end_le[ti]);
                                auto L2 = Lpol(e_ji.forward_line, bfj, bfi, end_le[tj]);

                                // AM1: L1 + L2 + clause + A_i_fwd + A_j_fwd +
                                // saturate. The B/F terms cancel against the
                                // active flags' AND-gate forward reifs, and
                                // the clause supplies the E_ij + E_ji >= 1
                                // that closes the case split.
                                PolBuilder am1;
                                am1.add(L1).add(L2).add(clause_line).add(bfi.active_fwd).add(bfj.active_fwd);
                                add_escape_pins(am1, reason, ti, tj);
                                return am1.saturate().emit(*logger, ProofLevel::Temporary);
                            };

                            auto atmost1_line = innards::recover_am1<ProofFlag>(
                                *logger, ProofLevel::Top,
                                vector<ProofFlag>{bf_i.active, bf_j.active},
                                function<ProofLine(const ProofFlag &, const ProofFlag &)>{pair_ne});

                            // Pol atmost1 with the two active=1 lines: the
                            // resulting constraint is infeasible under the
                            // bounds reason, and the framework's wrapping RUP
                            // step closes the contradiction.
                            PolBuilder{}
                                .add(atmost1_line)
                                .add(A_i_line)
                                .add(A_j_line)
                                .emit(*logger, ProofLevel::Temporary);
                        };

                        // The end-proxy pins use lb(l) for variable-length
                        // tasks, so those durations must be part of the reason.
                        auto reason_vars = starts;
                        if (is_var_len(pi))
                            reason_vars.push_back(length_vars[pi]);
                        if (is_var_len(pj))
                            reason_vars.push_back(length_vars[pj]);
                        inference.contradiction(logger,
                            JustifyExplicitly{justify, ThenRUP::Yes},
                            generic_reason(state, reason_vars));
                        return PropagatorState::DisableUntilBacktrack;
                    }

                // Variable durations join the reason for the push proofs (the
                // end-proxy materialisations and mandatory parts read lb(l)).
                // For a constant-only instance this is just the starts, leaving
                // the proof byte-identical.
                auto push_reason_vars = starts;
                for (auto i : active_tasks)
                    if (is_var_len(i))
                        push_reason_vars.push_back(length_vars[i]);

                // One step of an lb/ub-push chain: a blocked time t, the single
                // blocking task k (whose mandatory part covers t), and the start
                // lower bound that, with lb(l_j), forces after_{j,t} = 1 (the
                // running bound for lb-push, t - lb(l_j) + 1 for ub-push). For
                // h = 1, c = 1, one blocker is enough to overflow with j.
                struct ChainStep
                {
                    Integer t;
                    size_t k;
                    Integer s_lo_after;
                };

                // Per-step proof emitter, used for the lb-push chain. Mirrors
                // cumulative.cc's emit_chain_step, specialised to h = 1 and
                // c = 1, with the at-most-one supplied by the bridge instead
                // of an encoded C_t line. `ext_lit` is the running-bound
                // advance the step is meant to derive; `emit_intermediate`
                // controls whether ext_lit is then explicitly RUPped under
                // reason for the next step's preconditions to close.
                auto emit_chain_step = [&](size_t j, Integer t, size_t k,
                                           IntegerVariableCondition ext_lit, Integer s_lo_after,
                                           bool emit_intermediate, const ReasonLiterals & reason) -> void {
                    auto & bf_k = bridge->at(make_pair(k, t));
                    auto & bf_j = bridge->at(make_pair(j, t));

                    // (a) Pin A_{k,t} = 1 under reason via before / after /
                    // active. The mandatory blocker k has s_k + l_k >= lb(s_k) +
                    // lb(l_k) > t, so materialise its end before the after RUP.
                    logger->emit_rup_proof_line_under_reason(reason,
                        WPBSum{} + 1_i * bf_k.before >= 1_i, ProofLevel::Temporary);
                    materialise_end(k, state.lower_bound(starts[k]));
                    logger->emit_rup_proof_line_under_reason(reason,
                        WPBSum{} + 1_i * bf_k.after >= 1_i, ProofLevel::Temporary);
                    auto A_k_line = logger->emit_rup_proof_line_under_reason(reason,
                        WPBSum{} + 1_i * bf_k.active >= 1_i, ProofLevel::Temporary);

                    // (b) Pin A_{j,t} = 1 under extended reason {reason ∪
                    // ¬ext_lit}. Each line carries ext_lit as an extra
                    // disjunct, so VeriPB checks the RUP under
                    // "reason ∧ ¬ext_lit" which is exactly where j is also
                    // active at t. For a variable duration, s_lo_after + lb(l_j)
                    // >= t+1 materialises end_j so after_{j,t} = 1.
                    logger->emit_rup_proof_line_under_reason(reason,
                        WPBSum{} + 1_i * bf_j.before + 1_i * ext_lit >= 1_i,
                        ProofLevel::Temporary);
                    materialise_end(j, s_lo_after);
                    logger->emit_rup_proof_line_under_reason(reason,
                        WPBSum{} + 1_i * bf_j.after + 1_i * ext_lit >= 1_i,
                        ProofLevel::Temporary);
                    auto A_j_line = logger->emit_rup_proof_line_under_reason(reason,
                        WPBSum{} + 1_i * bf_j.active + 1_i * ext_lit >= 1_i,
                        ProofLevel::Temporary);

                    // (c) Pairwise at-most-one between A_{j,t} and A_{k,t} via
                    // recover_am1 + the same pair_ne pol as the contradiction
                    // proof (end_le threaded for variable durations).
                    map<ProofFlag, size_t> flag_to_task;
                    flag_to_task.emplace(bf_j.active, j);
                    flag_to_task.emplace(bf_k.active, k);
                    auto pair_ne = [&](const ProofFlag & a, const ProofFlag & b) -> ProofLine {
                        auto ti = flag_to_task.at(a);
                        auto tj = flag_to_task.at(b);
                        auto & bfi = bridge->at(make_pair(ti, t));
                        auto & bfj = bridge->at(make_pair(tj, t));
                        auto & e_ij = before_flags.at(make_pair(ti, tj));
                        auto & e_ji = before_flags.at(make_pair(tj, ti));
                        auto clause_line = clause_lines.at(
                            make_pair(min(ti, tj), max(ti, tj)));

                        auto Lpol = [&](ProofLine before_line, const BridgeFlags & aft,
                                        const BridgeFlags & bef, const optional<ProofLine> & aft_end_le) -> ProofLine {
                            PolBuilder pol;
                            pol.add(before_line).add(aft.after_fwd).add(bef.before_fwd);
                            if (aft_end_le)
                                pol.add(*aft_end_le);
                            return pol.saturate().emit(*logger, ProofLevel::Temporary);
                        };
                        auto L1 = Lpol(e_ij.forward_line, bfi, bfj, end_le[ti]);
                        auto L2 = Lpol(e_ji.forward_line, bfj, bfi, end_le[tj]);

                        PolBuilder am1;
                        am1.add(L1).add(L2).add(clause_line).add(bfi.active_fwd).add(bfj.active_fwd);
                        add_escape_pins(am1, reason, ti, tj);
                        return am1.saturate().emit(*logger, ProofLevel::Temporary);
                    };
                    auto atmost1_line = innards::recover_am1<ProofFlag>(
                        *logger, ProofLevel::Top,
                        vector<ProofFlag>{bf_j.active, bf_k.active},
                        function<ProofLine(const ProofFlag &, const ProofFlag &)>{pair_ne});

                    // (d) Pol atmost1 + A_k_line + A_j_line + saturate.
                    //   AM1:     ¬A_j + ¬A_k >= 1
                    //   A_k_line: A_k + ¬reason >= 1
                    //   A_j_line: A_j + ext_lit + ¬reason >= 1
                    //   Sum:     2 + ext_lit + 2·¬reason >= 3
                    //          = ext_lit + 2·¬reason >= 1
                    //   Saturated (RHS = 1):  ext_lit + ¬reason >= 1
                    // Under reason (¬reason = 0) this gives ext_lit = 1,
                    // which is the running-bound advance.
                    PolBuilder{}
                        .add(atmost1_line)
                        .add(A_k_line)
                        .add(A_j_line)
                        .saturate()
                        .emit(*logger, ProofLevel::Temporary);

                    // (e) Intermediate chain steps deposit ext_lit as an
                    // explicit RUP under reason so the next step's
                    // before/after RUPs can close: each of those needs
                    // s_j ≥ running_bound as a UP-derivable fact, and the
                    // pol's residual ¬reason disjuncts don't expose that
                    // cleanly enough for the next step. The final step
                    // doesn't need it — the framework's wrapping RUP
                    // (s_j ≥ new_lb) closes against the last pol directly.
                    if (emit_intermediate)
                        logger->emit_rup_proof_line_under_reason(reason,
                            WPBSum{} + 1_i * ext_lit >= 1_i, ProofLevel::Temporary);
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

                    auto is_blocked_at = [&](Integer t) -> bool {
                        auto load = mand_load[(t - t_lo).raw_value];
                        if (lst_j < eet_j && t >= lst_j && t < eet_j)
                            --load;
                        return load >= 1;
                    };

                    auto blocker_at = [&](Integer t) -> size_t {
                        // First task (≠ j) whose mandatory part covers t.
                        // One is enough for the h = 1, c = 1 chain step.
                        for (auto i : active_tasks) {
                            if (i == j || min_len(i) == 0_i)
                                continue;
                            auto lst_i = state.upper_bound(starts[i]);
                            auto eet_i = state.lower_bound(starts[i]) + min_len(i);
                            if (lst_i < eet_i && t >= lst_i && t < eet_i)
                                return i;
                        }
                        throw UnexpectedException{
                            "Disjunctive: is_blocked_at(t) true but no blocker found"};
                    };

                    // lb-push: scan upward to find the smallest fitting
                    // start, then chain through blocked times picking the
                    // LARGEST blocked t per step so the running lower bound
                    // advances as far as possible.
                    auto new_lb = cur_lb;
                    while (new_lb <= cur_ub && ! fits_at(new_lb))
                        ++new_lb;
                    if (new_lb > cur_lb) {
                        vector<ChainStep> chain;
                        Integer running_bound = cur_lb;
                        while (running_bound < new_lb) {
                            bool found = false;
                            for (Integer t = running_bound + min_len(j) - 1_i; t >= running_bound; --t)
                                if (is_blocked_at(t)) {
                                    chain.push_back(ChainStep{t, blocker_at(t), running_bound});
                                    running_bound = t + 1_i;
                                    found = true;
                                    break;
                                }
                            if (! found)
                                break;
                        }

                        auto justify = [&, j, chain](const ReasonLiterals & reason) -> void {
                            if (! logger || logger->get_assertion_level() > AssertionLevel::Off)
                                return;
                            for (size_t step = 0; step < chain.size(); ++step)
                                emit_chain_step(j, chain[step].t, chain[step].k,
                                    starts[j] > chain[step].t, chain[step].s_lo_after,
                                    step + 1 < chain.size(), reason);
                        };

                        inference.infer_greater_than_or_equal(logger, starts[j], new_lb,
                            JustifyExplicitly{justify, ThenRUP::Yes},
                            generic_reason(state, push_reason_vars));
                    }

                    // ub-push: mirror of lb-push, scanning downward. At each
                    // chain step pick the SMALLEST blocked t in the window
                    // [running_bound, running_bound + l_j - 1] so the
                    // running upper bound drops as far as possible. Each
                    // step turns a blocked t into the fact s_j < t - l_j + 1
                    // (equivalently s_j <= t - l_j); emit_chain_step's
                    // structure handles either push direction once given the
                    // right ext_lit.
                    auto new_ub = cur_ub;
                    while (new_ub >= cur_lb && ! fits_at(new_ub))
                        --new_ub;
                    if (new_ub < cur_ub) {
                        vector<ChainStep> chain;
                        Integer running_bound = cur_ub;
                        while (running_bound > new_ub) {
                            bool found = false;
                            for (Integer t = running_bound; t <= running_bound + min_len(j) - 1_i; ++t)
                                if (is_blocked_at(t)) {
                                    chain.push_back(ChainStep{t, blocker_at(t), t - min_len(j) + 1_i});
                                    running_bound = t - min_len(j);
                                    found = true;
                                    break;
                                }
                            if (! found)
                                break;
                        }

                        auto justify = [&, j, chain](const ReasonLiterals & reason) -> void {
                            if (! logger || logger->get_assertion_level() > AssertionLevel::Off)
                                return;
                            // ext_lit (s_j <= t - l_j) == (s_j < s_lo_after).
                            for (size_t step = 0; step < chain.size(); ++step)
                                emit_chain_step(j, chain[step].t, chain[step].k,
                                    starts[j] < chain[step].s_lo_after, chain[step].s_lo_after,
                                    step + 1 < chain.size(), reason);
                        };

                        inference.infer_less_than(logger, starts[j], new_ub + 1_i,
                            JustifyExplicitly{justify, ThenRUP::Yes},
                            generic_reason(state, push_reason_vars));
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
                        inference.contradiction(logger, JustifyUsingRUP{},
                            generic_reason(state, reason_vars));
                        return PropagatorState::DisableUntilBacktrack;
                    }
                }
            }

            return PropagatorState::Enable;
        },
        triggers);
}

auto Disjunctive::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    vector<SExpr> starts, lengths;
    for (const auto & v : _starts)
        starts.push_back(tracker.s_expr_term_of(v));
    for (const auto & l : _lengths)
        lengths.push_back(is_constant_variable(l)
                ? SExpr::atom(const_value_of(l).to_string())
                : tracker.s_expr_term_of(l));
    return SExpr::list({SExpr::atom(as_string(_constraint_id)),
        SExpr::atom(_strict ? "disjunctive_strict" : "disjunctive"),
        SExpr::list(std::move(starts)),
        SExpr::list(std::move(lengths))});
}
