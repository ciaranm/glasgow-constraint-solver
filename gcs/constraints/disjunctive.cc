#include <gcs/constraints/disjunctive.hh>
#include <gcs/constraints/innards/recover_am1.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <algorithm>
#include <functional>
#include <map>
#include <memory>
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

Disjunctive::Disjunctive(vector<IntegerVariableID> starts, vector<Integer> lengths, bool strict) :
    _starts(move(starts)),
    _lengths(move(lengths)),
    _strict(strict)
{
    if (_starts.size() != _lengths.size())
        throw UnexpectedException{"Disjunctive: starts and lengths must have the same size"};
    for (auto & l : _lengths)
        if (l < 0_i)
            throw UnexpectedException{"Disjunctive: lengths must be non-negative"};
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
    // In non-strict mode, zero-length tasks are dropped: they cannot constrain
    // any other task. In strict mode, every task participates (a zero-length
    // task at time t is forbidden from sitting strictly inside any other
    // task's active interval). Because lengths are constant, the distinction
    // is fully resolved here.
    auto n = _starts.size();
    _active_tasks.reserve(n);
    for (size_t i = 0; i < n; ++i) {
        if (! _strict && _lengths[i] == 0_i)
            continue;
        _active_tasks.push_back(i);
    }

    if (_active_tasks.size() < 2)
        return false;

    // Per-task possible-active window from root bounds. Only meaningful for
    // positive-length tasks; consumers gate on lengths[i] > 0_i.
    _per_task_t_lo.assign(n, 0_i);
    _per_task_t_hi.assign(n, 0_i);
    for (auto i : _active_tasks) {
        if (_lengths[i] == 0_i)
            continue;
        auto [s_lo, s_hi] = initial_state.bounds(_starts[i]);
        _per_task_t_lo[i] = s_lo;
        _per_task_t_hi[i] = s_hi + _lengths[i] - 1_i;
    }

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
    auto emit_before = [&](size_t i, size_t j) -> BeforeFlagData {
        auto flag = model.create_proof_flag("disjbefore");
        auto [fwd, rev] = model.add_two_way_reified_constraint(
            "Disjunctive", "first task finishes before second starts",
            WPBSum{} + 1_i * _starts[i] + -1_i * _starts[j] <= -_lengths[i],
            flag);
        if (! fwd || ! rev)
            throw UnexpectedException{"Disjunctive: pairwise reification half missing"};
        return BeforeFlagData{flag, *fwd, *rev};
    };
    for (size_t a = 0; a < _active_tasks.size(); ++a) {
        auto i = _active_tasks[a];
        for (size_t b = a + 1; b < _active_tasks.size(); ++b) {
            auto j = _active_tasks[b];
            auto data_ij = emit_before(i, j);
            auto data_ji = emit_before(j, i);
            auto clause = model.add_constraint("Disjunctive", "one task must finish first",
                WPBSum{} + 1_i * data_ij.flag + 1_i * data_ji.flag >= 1_i);
            if (! clause)
                throw UnexpectedException{"Disjunctive: pairwise clause missing"};
            _before_flags.emplace(std::make_pair(i, j), data_ij);
            _before_flags.emplace(std::make_pair(j, i), data_ji);
            _clause_lines.emplace(std::make_pair(i, j), *clause);
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
        ProofFlag after; // after_{i,t} <-> starts[i] >= t - lengths[i] + 1
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
        [starts = _starts, lengths = _lengths, active_tasks = _active_tasks,
            per_task_t_lo = _per_task_t_lo, per_task_t_hi = _per_task_t_hi,
            bridge](State &, auto &, ProofLogger * const logger) -> void {
            if (! logger)
                return;
            for (auto i : active_tasks) {
                if (lengths[i] == 0_i)
                    continue;
                for (Integer t = per_task_t_lo[i]; t <= per_task_t_hi[i]; ++t) {
                    auto [B, B_fwd, B_rev] = logger->create_proof_flag_reifying(
                        WPBSum{} + 1_i * starts[i] <= t,
                        "djbef", ProofLevel::Top);
                    auto [F, F_fwd, F_rev] = logger->create_proof_flag_reifying(
                        WPBSum{} + 1_i * starts[i] >= t - lengths[i] + 1_i,
                        "djaft", ProofLevel::Top);
                    auto [A, A_fwd, A_rev] = logger->create_proof_flag_reifying(
                        WPBSum{} + 1_i * B + 1_i * F >= 2_i,
                        "djact", ProofLevel::Top);
                    bridge->emplace(make_pair(i, t),
                        BridgeFlags{B, B_fwd, B_rev, F, F_fwd, F_rev, A, A_fwd, A_rev});
                }
            }
        });

    Triggers triggers;
    for (auto i : _active_tasks)
        triggers.on_bounds.emplace_back(_starts[i]);

    propagators.install(
        [starts = move(_starts), lengths = move(_lengths),
            active_tasks = move(_active_tasks),
            before_flags = move(_before_flags), clause_lines = move(_clause_lines),
            bridge](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
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
                if (lengths[i] == 0_i)
                    continue;
                auto [s_lo, s_hi] = state.bounds(starts[i]);
                auto lo = s_lo, hi = s_hi + lengths[i] - 1_i;
                if (! any || lo < t_lo) t_lo = lo;
                if (! any || hi > t_hi) t_hi = hi;
                any = true;
            }

            if (any) {
                auto range = (t_hi - t_lo + 1_i).raw_value;
                vector<int> mand_load(range, 0);

                for (auto i : active_tasks) {
                    if (lengths[i] == 0_i)
                        continue;
                    auto lst = state.upper_bound(starts[i]);
                    auto eet = state.lower_bound(starts[i]) + lengths[i];
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
                            if (lengths[i] == 0_i)
                                continue;
                            auto lst = state.upper_bound(starts[i]);
                            auto eet = state.lower_bound(starts[i]) + lengths[i];
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

                        auto justify = [logger, &before_flags, &clause_lines, &bridge,
                                           violating_t, pi, pj](const ReasonFunction & reason) -> void {
                            auto & bf_i = bridge->at(make_pair(pi, violating_t));
                            auto & bf_j = bridge->at(make_pair(pj, violating_t));

                            // Pin active_{*,vt} = 1 for both contributing tasks
                            // under the bounds reason. Cumulative-style chain:
                            // before, then after, then active — VeriPB UP can't
                            // chase through the AND-gate of active's reverse
                            // half in a single step.
                            logger->emit_rup_proof_line_under_reason(reason,
                                WPBSum{} + 1_i * bf_i.before >= 1_i, ProofLevel::Temporary);
                            logger->emit_rup_proof_line_under_reason(reason,
                                WPBSum{} + 1_i * bf_i.after >= 1_i, ProofLevel::Temporary);
                            auto A_i_line = logger->emit_rup_proof_line_under_reason(reason,
                                WPBSum{} + 1_i * bf_i.active >= 1_i, ProofLevel::Temporary);
                            logger->emit_rup_proof_line_under_reason(reason,
                                WPBSum{} + 1_i * bf_j.before >= 1_i, ProofLevel::Temporary);
                            logger->emit_rup_proof_line_under_reason(reason,
                                WPBSum{} + 1_i * bf_j.after >= 1_i, ProofLevel::Temporary);
                            auto A_j_line = logger->emit_rup_proof_line_under_reason(reason,
                                WPBSum{} + 1_i * bf_j.active >= 1_i, ProofLevel::Temporary);

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

                            auto pair_ne = [logger, &before_flags, &clause_lines, &bridge,
                                               violating_t, &flag_to_task](
                                               const ProofFlag & a, const ProofFlag & b) -> ProofLine {
                                auto ti = flag_to_task.at(a);
                                auto tj = flag_to_task.at(b);
                                auto & bfi = bridge->at(make_pair(ti, violating_t));
                                auto & bfj = bridge->at(make_pair(tj, violating_t));
                                auto & e_ij = before_flags.at(make_pair(ti, tj));
                                auto & e_ji = before_flags.at(make_pair(tj, ti));
                                auto clause_line = clause_lines.at(
                                    make_pair(min(ti, tj), max(ti, tj)));

                                // L1: E_ij_fwd + F_i_fwd + B_j_fwd + saturate.
                                // (s_j - s_i) + s_i + (-s_j) = 0, RHS = 1.
                                // Result: ¬E_ij + ¬F_i + ¬B_j >= 1.
                                stringstream pol1;
                                pol1 << "pol " << e_ij.forward_line
                                     << " " << bfi.after_fwd << " +"
                                     << " " << bfj.before_fwd << " +"
                                     << " s ;";
                                auto L1 = logger->emit_proof_line(pol1.str(), ProofLevel::Temporary);

                                // L2: symmetric, swapping roles of i and j.
                                stringstream pol2;
                                pol2 << "pol " << e_ji.forward_line
                                     << " " << bfj.after_fwd << " +"
                                     << " " << bfi.before_fwd << " +"
                                     << " s ;";
                                auto L2 = logger->emit_proof_line(pol2.str(), ProofLevel::Temporary);

                                // AM1: L1 + L2 + clause + A_i_fwd + A_j_fwd +
                                // saturate. The B/F terms cancel against the
                                // active flags' AND-gate forward reifs, and
                                // the clause supplies the E_ij + E_ji >= 1
                                // that closes the case split.
                                stringstream pol3;
                                pol3 << "pol " << L1
                                     << " " << L2 << " +"
                                     << " " << clause_line << " +"
                                     << " " << bfi.active_fwd << " +"
                                     << " " << bfj.active_fwd << " +"
                                     << " s ;";
                                return logger->emit_proof_line(pol3.str(), ProofLevel::Temporary);
                            };

                            auto atmost1_line = innards::recover_am1<ProofFlag>(
                                *logger, ProofLevel::Top,
                                vector<ProofFlag>{bf_i.active, bf_j.active},
                                function<ProofLine(const ProofFlag &, const ProofFlag &)>{pair_ne});

                            // Pol atmost1 with the two active=1 lines: the
                            // resulting constraint is infeasible under the
                            // bounds reason, and the framework's wrapping RUP
                            // step closes the contradiction.
                            stringstream final_pol;
                            final_pol << "pol " << atmost1_line
                                      << " " << A_i_line << " +"
                                      << " " << A_j_line << " +"
                                      << " ;";
                            logger->emit_proof_line(final_pol.str(), ProofLevel::Temporary);
                        };

                        inference.contradiction(logger,
                            JustifyExplicitlyThenRUP{justify},
                            generic_reason(state, starts));
                        return PropagatorState::DisableUntilBacktrack;
                    }

                // One step of an lb/ub-push chain: a blocked time t and the
                // single blocking task k (whose mandatory part covers t).
                // For h = 1, c = 1, one blocker is enough to overflow with j.
                struct ChainStep
                {
                    Integer t;
                    size_t k;
                };

                // Per-step proof emitter, used for the lb-push chain. Mirrors
                // cumulative.cc's emit_chain_step, specialised to h = 1 and
                // c = 1, with the at-most-one supplied by the bridge instead
                // of an encoded C_t line. `ext_lit` is the running-bound
                // advance the step is meant to derive; `emit_intermediate`
                // controls whether ext_lit is then explicitly RUPped under
                // reason for the next step's preconditions to close.
                auto emit_chain_step = [logger, &before_flags, &clause_lines, &bridge](
                                           size_t j, Integer t, size_t k,
                                           IntegerVariableCondition ext_lit,
                                           bool emit_intermediate,
                                           const ReasonFunction & reason) -> void {
                    auto & bf_k = bridge->at(make_pair(k, t));
                    auto & bf_j = bridge->at(make_pair(j, t));

                    // (a) Pin A_{k,t} = 1 under reason via before / after / active.
                    logger->emit_rup_proof_line_under_reason(reason,
                        WPBSum{} + 1_i * bf_k.before >= 1_i, ProofLevel::Temporary);
                    logger->emit_rup_proof_line_under_reason(reason,
                        WPBSum{} + 1_i * bf_k.after >= 1_i, ProofLevel::Temporary);
                    auto A_k_line = logger->emit_rup_proof_line_under_reason(reason,
                        WPBSum{} + 1_i * bf_k.active >= 1_i, ProofLevel::Temporary);

                    // (b) Pin A_{j,t} = 1 under extended reason {reason ∪
                    // ¬ext_lit}. Each line carries ext_lit as an extra
                    // disjunct, so VeriPB checks the RUP under
                    // "reason ∧ ¬ext_lit" which is exactly where j is also
                    // active at t.
                    logger->emit_rup_proof_line_under_reason(reason,
                        WPBSum{} + 1_i * bf_j.before + 1_i * ext_lit >= 1_i,
                        ProofLevel::Temporary);
                    logger->emit_rup_proof_line_under_reason(reason,
                        WPBSum{} + 1_i * bf_j.after + 1_i * ext_lit >= 1_i,
                        ProofLevel::Temporary);
                    auto A_j_line = logger->emit_rup_proof_line_under_reason(reason,
                        WPBSum{} + 1_i * bf_j.active + 1_i * ext_lit >= 1_i,
                        ProofLevel::Temporary);

                    // (c) Pairwise at-most-one between A_{j,t} and A_{k,t} via
                    // recover_am1 + the same three-step pair_ne pol as the
                    // contradiction proof.
                    map<ProofFlag, size_t> flag_to_task;
                    flag_to_task.emplace(bf_j.active, j);
                    flag_to_task.emplace(bf_k.active, k);
                    auto pair_ne = [logger, &before_flags, &clause_lines, &bridge,
                                       t, &flag_to_task](
                                       const ProofFlag & a, const ProofFlag & b) -> ProofLine {
                        auto ti = flag_to_task.at(a);
                        auto tj = flag_to_task.at(b);
                        auto & bfi = bridge->at(make_pair(ti, t));
                        auto & bfj = bridge->at(make_pair(tj, t));
                        auto & e_ij = before_flags.at(make_pair(ti, tj));
                        auto & e_ji = before_flags.at(make_pair(tj, ti));
                        auto clause_line = clause_lines.at(
                            make_pair(min(ti, tj), max(ti, tj)));

                        stringstream pol1;
                        pol1 << "pol " << e_ij.forward_line
                             << " " << bfi.after_fwd << " +"
                             << " " << bfj.before_fwd << " +"
                             << " s ;";
                        auto L1 = logger->emit_proof_line(pol1.str(), ProofLevel::Temporary);

                        stringstream pol2;
                        pol2 << "pol " << e_ji.forward_line
                             << " " << bfj.after_fwd << " +"
                             << " " << bfi.before_fwd << " +"
                             << " s ;";
                        auto L2 = logger->emit_proof_line(pol2.str(), ProofLevel::Temporary);

                        stringstream pol3;
                        pol3 << "pol " << L1
                             << " " << L2 << " +"
                             << " " << clause_line << " +"
                             << " " << bfi.active_fwd << " +"
                             << " " << bfj.active_fwd << " +"
                             << " s ;";
                        return logger->emit_proof_line(pol3.str(), ProofLevel::Temporary);
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
                    stringstream pol;
                    pol << "pol " << atmost1_line
                        << " " << A_k_line << " +"
                        << " " << A_j_line << " +"
                        << " s ;";
                    logger->emit_proof_line(pol.str(), ProofLevel::Temporary);

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
                    if (lengths[j] == 0_i)
                        continue;
                    auto [cur_lb, cur_ub] = state.bounds(starts[j]);
                    if (cur_lb == cur_ub)
                        continue;

                    auto lst_j = cur_ub, eet_j = cur_lb + lengths[j];
                    auto fits_at = [&](Integer s) -> bool {
                        for (Integer t = s; t < s + lengths[j]; ++t) {
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
                            if (i == j || lengths[i] == 0_i)
                                continue;
                            auto lst_i = state.upper_bound(starts[i]);
                            auto eet_i = state.lower_bound(starts[i]) + lengths[i];
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
                            for (Integer t = running_bound + lengths[j] - 1_i; t >= running_bound; --t)
                                if (is_blocked_at(t)) {
                                    chain.push_back(ChainStep{t, blocker_at(t)});
                                    running_bound = t + 1_i;
                                    found = true;
                                    break;
                                }
                            if (! found)
                                break;
                        }

                        auto justify = [&, j, chain](const ReasonFunction & reason) -> void {
                            if (! logger)
                                return;
                            for (size_t step = 0; step < chain.size(); ++step)
                                emit_chain_step(j, chain[step].t, chain[step].k,
                                    starts[j] >= chain[step].t + 1_i,
                                    step + 1 < chain.size(), reason);
                        };

                        inference.infer_greater_than_or_equal(logger, starts[j], new_lb,
                            JustifyExplicitlyThenRUP{justify},
                            generic_reason(state, starts));
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
                            for (Integer t = running_bound; t <= running_bound + lengths[j] - 1_i; ++t)
                                if (is_blocked_at(t)) {
                                    chain.push_back(ChainStep{t, blocker_at(t)});
                                    running_bound = t - lengths[j];
                                    found = true;
                                    break;
                                }
                            if (! found)
                                break;
                        }

                        auto justify = [&, j, chain](const ReasonFunction & reason) -> void {
                            if (! logger)
                                return;
                            for (size_t step = 0; step < chain.size(); ++step)
                                emit_chain_step(j, chain[step].t, chain[step].k,
                                    starts[j] < chain[step].t - lengths[j] + 1_i,
                                    step + 1 < chain.size(), reason);
                        };

                        inference.infer_less_than(logger, starts[j], new_ub + 1_i,
                            JustifyExplicitlyThenRUP{justify},
                            generic_reason(state, starts));
                    }
                }
            }

            // Strict-mode zero-length tasks: check that no fixed zero-length
            // task sits strictly inside a fixed positive-length task's open
            // active interval. (Non-strict mode never sees zero-length tasks
            // in active_tasks — they were dropped at prepare() time.)
            //
            // The proof is JustifyUsingRUP: at the all-fixed leaf, the
            // declarative pairwise encoding alone is enough. With s_z and
            // s_k fixed at vz, vk satisfying vk < vz < vk + l_k,
            // before_{z,k} = (vz <= vk) UPs to 0 and before_{k,z} =
            // (vk + l_k <= vz) UPs to 0, contradicting the encoded clause
            // before_{z,k} + before_{k,z} >= 1.
            for (auto z : active_tasks) {
                if (lengths[z] > 0_i)
                    continue;
                if (! state.has_single_value(starts[z]))
                    continue;
                auto vz = state.lower_bound(starts[z]);
                for (auto k : active_tasks) {
                    if (k == z || lengths[k] == 0_i)
                        continue;
                    if (! state.has_single_value(starts[k]))
                        continue;
                    auto vk = state.lower_bound(starts[k]);
                    if (vk < vz && vz < vk + lengths[k]) {
                        inference.contradiction(logger, JustifyUsingRUP{},
                            generic_reason(state, starts));
                        return PropagatorState::DisableUntilBacktrack;
                    }
                }
            }

            return PropagatorState::Enable;
        },
        triggers);
}

auto Disjunctive::s_exprify(const ProofModel * const model) const -> string
{
    stringstream s;
    print(s, "{} disjunctive{} (", _name, _strict ? "_strict" : "");
    for (const auto & v : _starts)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(v));
    print(s, " ) ( ");
    for (const auto & l : _lengths)
        print(s, " {}", l);
    print(s, " )");
    return s.str();
}
