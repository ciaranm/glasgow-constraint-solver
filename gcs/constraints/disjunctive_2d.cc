#include <gcs/constraints/disjunctive_2d.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
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

Disjunctive2D::Disjunctive2D(vector<IntegerVariableID> xs, vector<IntegerVariableID> ys,
    vector<Integer> widths, vector<Integer> heights, bool strict) :
    _xs(move(xs)),
    _ys(move(ys)),
    _widths(move(widths)),
    _heights(move(heights)),
    _strict(strict)
{
    if (_xs.size() != _ys.size() || _xs.size() != _widths.size() || _xs.size() != _heights.size())
        throw InvalidProblemDefinitionException{"Disjunctive2D: xs, ys, widths, heights must have the same size"};
    for (auto & w : _widths)
        if (w < 0_i)
            throw InvalidProblemDefinitionException{"Disjunctive2D: widths must be non-negative"};
    for (auto & h : _heights)
        if (h < 0_i)
            throw InvalidProblemDefinitionException{"Disjunctive2D: heights must be non-negative"};
}

auto Disjunctive2D::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Disjunctive2D>(_xs, _ys, _widths, _heights, _strict);
}

auto Disjunctive2D::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto Disjunctive2D::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    // In non-strict mode, a zero-area rectangle (width 0 or height 0) cannot
    // overlap anything and is dropped. In strict mode every rectangle
    // participates; with the <= separation clause a zero-size rectangle can
    // always separate, so it never forces an overlap, but its pairwise clauses
    // remain in the OPB for leaf correctness.
    auto n = _xs.size();
    _active_rects.reserve(n);
    for (size_t i = 0; i < n; ++i) {
        if (! _strict && (_widths[i] == 0_i || _heights[i] == 0_i))
            continue;
        _active_rects.push_back(i);
    }

    if (_active_rects.size() < 2)
        return false;

    _x_lo.assign(n, 0_i);
    _x_hi.assign(n, 0_i);
    _y_lo.assign(n, 0_i);
    _y_hi.assign(n, 0_i);
    for (auto i : _active_rects) {
        auto [x_lo, x_hi] = initial_state.bounds(_xs[i]);
        auto [y_lo, y_hi] = initial_state.bounds(_ys[i]);
        _x_lo[i] = x_lo;
        _x_hi[i] = x_hi + _widths[i] - 1_i;
        _y_lo[i] = y_lo;
        _y_hi[i] = y_hi + _heights[i] - 1_i;
    }

    return true;
}

auto Disjunctive2D::define_proof_model(ProofModel & model) -> void
{
    // Declarative pairwise OPB encoding (the diffn definition itself):
    //   for each axis d in {x, y} and ordered pair (i, j):
    //     before_{i,j,d} <-> pos_{i,d} + size_{i,d} <= pos_{j,d}
    //   then one separation clause per unordered pair:
    //     before_{i,j,x} + before_{j,i,x} + before_{i,j,y} + before_{j,i,y} >= 1
    //
    // Nothing propagator-specific goes into the OPB; the bridge to per-(rect,
    // coordinate) time-table flags is introduced by install_propagators's
    // initialiser, scoped to the proof.
    auto emit_before = [&](const vector<IntegerVariableID> & pos, const vector<Integer> & size,
                           size_t i, size_t j) -> BeforeFlagData {
        auto flag = model.create_proof_flag("disj2dbefore");
        auto [fwd, rev] = model.add_two_way_reified_constraint(
            "Disjunctive2D", "first rectangle precedes second on this axis",
            WPBSum{} + 1_i * pos[i] + -1_i * pos[j] <= -size[i],
            flag);
        if (! fwd || ! rev)
            throw UnexpectedException{"Disjunctive2D: pairwise reification half missing"};
        return BeforeFlagData{flag, *fwd, *rev};
    };

    for (size_t a = 0; a < _active_rects.size(); ++a) {
        auto i = _active_rects[a];
        for (size_t b = a + 1; b < _active_rects.size(); ++b) {
            auto j = _active_rects[b];
            auto bx_ij = emit_before(_xs, _widths, i, j);
            auto bx_ji = emit_before(_xs, _widths, j, i);
            auto by_ij = emit_before(_ys, _heights, i, j);
            auto by_ji = emit_before(_ys, _heights, j, i);
            auto clause = model.add_constraint("Disjunctive2D", "rectangles must be separated on some axis",
                WPBSum{} + 1_i * bx_ij.flag + 1_i * bx_ji.flag + 1_i * by_ij.flag + 1_i * by_ji.flag >= 1_i);
            if (! clause)
                throw UnexpectedException{"Disjunctive2D: separation clause missing"};
            _before_x.emplace(make_pair(i, j), bx_ij);
            _before_x.emplace(make_pair(j, i), bx_ji);
            _before_y.emplace(make_pair(i, j), by_ij);
            _before_y.emplace(make_pair(j, i), by_ji);
            _clause_lines.emplace(make_pair(i, j), *clause);
        }
    }
}

namespace
{
    // Per-(rect, coordinate) bridge flags introduced by install_propagators's
    // initialiser at search root, one set per axis. They connect the
    // declarative pairwise OPB encoding to the time-table reasoning the
    // propagator uses, but live entirely in the proof database (not the OPB).
    // "before" here means "rect starts at or before this coordinate" and
    // "after" means "rect has not yet finished at this coordinate"; their
    // conjunction "active" means the rect spans the coordinate on that axis.
    struct BridgeFlags
    {
        ProofFlag before;
        ProofLine before_fwd, before_rev;
        ProofFlag after;
        ProofLine after_fwd, after_rev;
        ProofFlag active;
        ProofLine active_fwd, active_rev;
    };
    using BridgeMap = map<pair<size_t, Integer>, BridgeFlags>;
}

auto Disjunctive2D::install_propagators(Propagators & propagators) -> void
{
    // The OPB stays declarative (the pairwise separation clauses). The bridge
    // to per-(rect, coordinate) before/after/active flags is propagator
    // scaffolding, pre-emitted once at search root at ProofLevel::Top so the
    // flags survive the whole search (Glasgow has no flag-deletion API, so
    // eager root-time emission bounds the total to O(n * (W + H)) flags).
    auto bridge_x = make_shared<BridgeMap>();
    auto bridge_y = make_shared<BridgeMap>();

    propagators.install_initialiser(
        [xs = _xs, ys = _ys, widths = _widths, heights = _heights, active_rects = _active_rects,
            x_lo = _x_lo, x_hi = _x_hi, y_lo = _y_lo, y_hi = _y_hi, bridge_x, bridge_y](
            State &, auto &, ProofLogger * const logger) -> void {
            if (! logger)
                return;
            auto emit_axis = [&](BridgeMap & bridge, const vector<IntegerVariableID> & pos,
                                 const vector<Integer> & size, size_t i, Integer lo, Integer hi) {
                for (Integer t = lo; t <= hi; ++t) {
                    auto [B, B_fwd, B_rev] = logger->create_proof_flag_reifying(
                        WPBSum{} + 1_i * pos[i] <= t, "d2dbef", ProofLevel::Top);
                    auto [F, F_fwd, F_rev] = logger->create_proof_flag_reifying(
                        WPBSum{} + 1_i * pos[i] >= t - size[i] + 1_i, "d2daft", ProofLevel::Top);
                    auto [A, A_fwd, A_rev] = logger->create_proof_flag_reifying(
                        WPBSum{} + 1_i * B + 1_i * F >= 2_i, "d2dact", ProofLevel::Top);
                    bridge.emplace(make_pair(i, t),
                        BridgeFlags{B, B_fwd, B_rev, F, F_fwd, F_rev, A, A_fwd, A_rev});
                }
            };
            for (auto i : active_rects) {
                if (widths[i] > 0_i)
                    emit_axis(*bridge_x, xs, widths, i, x_lo[i], x_hi[i]);
                if (heights[i] > 0_i)
                    emit_axis(*bridge_y, ys, heights, i, y_lo[i], y_hi[i]);
            }
        });

    Triggers triggers;
    for (auto i : _active_rects) {
        triggers.on_bounds.emplace_back(_xs[i]);
        triggers.on_bounds.emplace_back(_ys[i]);
    }

    propagators.install(
        [xs = move(_xs), ys = move(_ys), widths = move(_widths), heights = move(_heights),
            active_rects = move(_active_rects), before_x = move(_before_x), before_y = move(_before_y),
            clause_lines = move(_clause_lines), bridge_x, bridge_y](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // Pairwise 2D time-table. The mandatory box of rectangle i is
            //   [ub(x_i), lb(x_i)+w_i) x [ub(y_i), lb(y_i)+h_i)
            // -- the cells it must occupy regardless of where it is placed. Two
            // rectangles whose mandatory boxes overlap is infeasible.
            //
            // Bound pushes (a forced overlap on one axis pushes the other) land
            // in S1c; the contradiction here is still proof-logged via an
            // assertion until S1b replaces it with the bridge derivation.
            auto mand = [&](IntegerVariableID pos, Integer size) -> pair<Integer, Integer> {
                return {state.upper_bound(pos), state.lower_bound(pos) + size};
            };

            for (size_t a = 0; a < active_rects.size(); ++a) {
                auto i = active_rects[a];
                auto [lst_xi, eet_xi] = mand(xs[i], widths[i]);
                auto [lst_yi, eet_yi] = mand(ys[i], heights[i]);
                if (lst_xi >= eet_xi || lst_yi >= eet_yi)
                    continue;
                for (size_t b = a + 1; b < active_rects.size(); ++b) {
                    auto j = active_rects[b];
                    auto [lst_xj, eet_xj] = mand(xs[j], widths[j]);
                    auto [lst_yj, eet_yj] = mand(ys[j], heights[j]);
                    if (lst_xj >= eet_xj || lst_yj >= eet_yj)
                        continue;
                    auto x_overlap = max(lst_xi, lst_xj) < min(eet_xi, eet_xj);
                    auto y_overlap = max(lst_yi, lst_yj) < min(eet_yi, eet_yj);
                    if (x_overlap && y_overlap) {
                        // Pick a cell (p, q) inside both mandatory boxes.
                        auto p = max(lst_xi, lst_xj);
                        auto q = max(lst_yi, lst_yj);

                        auto justify = [logger, &before_x, &before_y, &clause_lines,
                                           &bridge_x, &bridge_y, i, j, p, q](
                                           const ReasonFunction & reason) -> void {
                            // Pin "rect r spans coord on this axis" = 1 under the
                            // bounds reason: before, then after, then active (UP
                            // can't chase active's AND-gate in one step).
                            auto pin = [&](BridgeMap & bridge, Integer coord, size_t r) -> ProofLine {
                                auto & bf = bridge.at(make_pair(r, coord));
                                logger->emit_rup_proof_line_under_reason(reason,
                                    WPBSum{} + 1_i * bf.before >= 1_i, ProofLevel::Temporary);
                                logger->emit_rup_proof_line_under_reason(reason,
                                    WPBSum{} + 1_i * bf.after >= 1_i, ProofLevel::Temporary);
                                return logger->emit_rup_proof_line_under_reason(reason,
                                    WPBSum{} + 1_i * bf.active >= 1_i, ProofLevel::Temporary);
                            };
                            auto Ax_i = pin(*bridge_x, p, i);
                            auto Ay_i = pin(*bridge_y, q, i);
                            auto Ax_j = pin(*bridge_x, p, j);
                            auto Ay_j = pin(*bridge_y, q, j);

                            auto & bx_i = bridge_x->at(make_pair(i, p));
                            auto & bx_j = bridge_x->at(make_pair(j, p));
                            auto & by_i = bridge_y->at(make_pair(i, q));
                            auto & by_j = bridge_y->at(make_pair(j, q));

                            // For each axis/direction, derive "the precedence
                            // flag is false given both rects span the cell": the
                            // integer terms cancel (cf. 1D Disjunctive pair_ne).
                            auto Lpol = [&](const BeforeFlagData & bf_ab, const BridgeFlags & aft_a,
                                            const BridgeFlags & bef_b) -> ProofLine {
                                return PolBuilder{}
                                    .add(bf_ab.forward_line)
                                    .add(aft_a.after_fwd)
                                    .add(bef_b.before_fwd)
                                    .saturate()
                                    .emit(*logger, ProofLevel::Temporary);
                            };
                            auto Lx1 = Lpol(before_x.at(make_pair(i, j)), bx_i, bx_j);
                            auto Lx2 = Lpol(before_x.at(make_pair(j, i)), bx_j, bx_i);
                            auto Ly1 = Lpol(before_y.at(make_pair(i, j)), by_i, by_j);
                            auto Ly2 = Lpol(before_y.at(make_pair(j, i)), by_j, by_i);

                            // Combine the four precedence-false lines with the
                            // 4-way separation clause and the four active AND-gate
                            // forward reifs: the precedence and before/after terms
                            // cancel, leaving "not all four spans hold".
                            auto not_all = PolBuilder{}
                                               .add(clause_lines.at(make_pair(min(i, j), max(i, j))))
                                               .add(Lx1)
                                               .add(Lx2)
                                               .add(Ly1)
                                               .add(Ly2)
                                               .add(bx_i.active_fwd)
                                               .add(bx_j.active_fwd)
                                               .add(by_i.active_fwd)
                                               .add(by_j.active_fwd)
                                               .saturate()
                                               .emit(*logger, ProofLevel::Temporary);

                            // Pol "not all four spans" against the four pinned
                            // spans: infeasible under the reason, closing the
                            // framework's wrapping RUP.
                            PolBuilder{}
                                .add(not_all)
                                .add(Ax_i)
                                .add(Ay_i)
                                .add(Ax_j)
                                .add(Ay_j)
                                .emit(*logger, ProofLevel::Temporary);
                        };

                        inference.contradiction(logger, JustifyExplicitlyThenRUP{justify},
                            generic_reason(state, vector<IntegerVariableID>{xs[i], ys[i], xs[j], ys[j]}));
                        return PropagatorState::DisableUntilBacktrack;
                    }
                }
            }

            // Pairwise bound pushes. A pair whose mandatory parts overlap on one
            // axis (the "forced" axis) must separate on the other (the "free"
            // axis) -- no pair overlaps on both, since the contradiction pass
            // returned otherwise. So the pushed rectangle is moved clear of the
            // blocker's mandatory part on the free axis: a 1D single-blocker
            // disjunctive push, justified by deriving the reduced clause
            // by_ij + by_ji >= 1 from the forced-axis overlap and then running a
            // 1D-style chain against it on the free axis.
            //
            // free_*: the axis we push on; forced_*: the axis they overlap on;
            // i is pushed, j blocks, forced_col is a column both span on the
            // forced axis.
            auto push_axis = [&](const vector<IntegerVariableID> & free_pos, const vector<Integer> & free_size,
                                 BridgeMap & free_bridge, const std::map<pair<size_t, size_t>, BeforeFlagData> & free_before,
                                 BridgeMap & forced_bridge, const std::map<pair<size_t, size_t>, BeforeFlagData> & forced_before,
                                 size_t i, size_t j, Integer forced_col) {
                auto sz = free_size[i];
                if (sz == 0_i)
                    return; // a zero-size rectangle spans no cells on this axis
                auto [cur_lo, cur_hi] = state.bounds(free_pos[i]);
                auto blk_lo = state.upper_bound(free_pos[j]);
                auto blk_hi = state.lower_bound(free_pos[j]) + free_size[j];
                if (blk_lo >= blk_hi)
                    return; // blocker has no mandatory part on the free axis
                auto is_blocked = [&](Integer t) { return t >= blk_lo && t < blk_hi; };

                vector<IntegerVariableID> rv{xs[i], ys[i], xs[j], ys[j]};

                // Emit the reduced clause by_ij + by_ji >= 1 (forced-axis
                // elimination), then one chain step per blocked free-cell. dir
                // = +1 for an lb-push (ext_lit: pos > t), -1 for a ub-push
                // (ext_lit: pos < t - sz + 1).
                auto emit_proof = [&, i, j, forced_col, sz](const vector<Integer> & chain, int dir,
                                      const ReasonFunction & reason) {
                    auto pin = [&](BridgeMap & bridge, Integer coord, size_t r) -> ProofLine {
                        auto & bf = bridge.at(make_pair(r, coord));
                        logger->emit_rup_proof_line_under_reason(reason,
                            WPBSum{} + 1_i * bf.before >= 1_i, ProofLevel::Temporary);
                        logger->emit_rup_proof_line_under_reason(reason,
                            WPBSum{} + 1_i * bf.after >= 1_i, ProofLevel::Temporary);
                        return logger->emit_rup_proof_line_under_reason(reason,
                            WPBSum{} + 1_i * bf.active >= 1_i, ProofLevel::Temporary);
                    };
                    auto Lpol = [&](const BeforeFlagData & bf_ab, const BridgeFlags & aft_a,
                                    const BridgeFlags & bef_b) -> ProofLine {
                        return PolBuilder{}.add(bf_ab.forward_line).add(aft_a.after_fwd).add(bef_b.before_fwd).saturate().emit(*logger, ProofLevel::Temporary);
                    };

                    // Forced-axis elimination: both rects span forced_col, so
                    // neither forced-axis precedence holds; with the 4-way clause
                    // that leaves the free-axis disjunction.
                    auto Ax_i = pin(forced_bridge, forced_col, i);
                    auto Ax_j = pin(forced_bridge, forced_col, j);
                    auto & fx_i = forced_bridge.at(make_pair(i, forced_col));
                    auto & fx_j = forced_bridge.at(make_pair(j, forced_col));
                    auto Lf1 = Lpol(forced_before.at(make_pair(i, j)), fx_i, fx_j);
                    auto Lf2 = Lpol(forced_before.at(make_pair(j, i)), fx_j, fx_i);
                    auto reduced = PolBuilder{}
                                       .add(clause_lines.at(make_pair(min(i, j), max(i, j))))
                                       .add(Lf1)
                                       .add(Lf2)
                                       .add(fx_i.active_fwd)
                                       .add(fx_j.active_fwd)
                                       .add(Ax_i)
                                       .add(Ax_j)
                                       .saturate()
                                       .emit(*logger, ProofLevel::Temporary);

                    // Free-axis chain: at each blocked cell t, both i (under the
                    // running bound / ext_lit) and j span t, contradicting the
                    // reduced clause, forcing the bound advance ext_lit.
                    for (size_t step = 0; step < chain.size(); ++step) {
                        auto t = chain[step];
                        auto ext_lit = dir > 0 ? (free_pos[i] > t) : (free_pos[i] < t - sz + 1_i);
                        auto A_blk = pin(free_bridge, t, j);
                        auto & fy_i = free_bridge.at(make_pair(i, t));
                        auto & fy_j = free_bridge.at(make_pair(j, t));
                        logger->emit_rup_proof_line_under_reason(reason,
                            WPBSum{} + 1_i * fy_i.before + 1_i * ext_lit >= 1_i, ProofLevel::Temporary);
                        logger->emit_rup_proof_line_under_reason(reason,
                            WPBSum{} + 1_i * fy_i.after + 1_i * ext_lit >= 1_i, ProofLevel::Temporary);
                        auto A_psh = logger->emit_rup_proof_line_under_reason(reason,
                            WPBSum{} + 1_i * fy_i.active + 1_i * ext_lit >= 1_i, ProofLevel::Temporary);
                        auto Ly1 = Lpol(free_before.at(make_pair(i, j)), fy_i, fy_j);
                        auto Ly2 = Lpol(free_before.at(make_pair(j, i)), fy_j, fy_i);
                        auto not_both = PolBuilder{}
                                            .add(Ly1)
                                            .add(Ly2)
                                            .add(reduced)
                                            .add(fy_i.active_fwd)
                                            .add(fy_j.active_fwd)
                                            .saturate()
                                            .emit(*logger, ProofLevel::Temporary);
                        PolBuilder{}.add(not_both).add(A_blk).add(A_psh).saturate().emit(*logger, ProofLevel::Temporary);
                        if (step + 1 < chain.size())
                            logger->emit_rup_proof_line_under_reason(reason,
                                WPBSum{} + 1_i * ext_lit >= 1_i, ProofLevel::Temporary);
                    }
                };

                // lb-push: i cannot fit below the blocker, push its origin up to
                // blk_hi -- but capped at cur_hi + 1, since beyond that the
                // domain is already empty (i cannot fit above either) and the
                // chain would reference free cells i can never span. The capped
                // bound is weaker but sound, and empties the domain to a
                // contradiction when needed.
                if (cur_lo > blk_lo - sz && cur_lo < blk_hi) {
                    auto target = min(blk_hi, cur_hi + 1_i);
                    vector<Integer> chain;
                    Integer running = cur_lo;
                    while (running < target) {
                        bool found = false;
                        for (Integer t = running + sz - 1_i; t >= running; --t)
                            if (is_blocked(t)) {
                                chain.push_back(t);
                                running = t + 1_i;
                                found = true;
                                break;
                            }
                        if (! found)
                            break;
                    }
                    auto justify = [&, chain](const ReasonFunction & reason) -> void {
                        if (logger)
                            emit_proof(chain, +1, reason);
                    };
                    inference.infer_greater_than_or_equal(logger, free_pos[i], target,
                        JustifyExplicitlyThenRUP{justify}, generic_reason(state, rv));
                }
                // ub-push: i cannot fit above the blocker, push its origin down to
                // blk_lo - sz -- capped at cur_lo - 1 by the same reasoning.
                else if (cur_hi > blk_lo - sz && cur_hi < blk_hi) {
                    auto target = max(blk_lo - sz, cur_lo - 1_i);
                    vector<Integer> chain;
                    Integer running = cur_hi;
                    while (running > target) {
                        bool found = false;
                        for (Integer t = running; t <= running + sz - 1_i; ++t)
                            if (is_blocked(t)) {
                                chain.push_back(t);
                                running = t - sz;
                                found = true;
                                break;
                            }
                        if (! found)
                            break;
                    }
                    auto justify = [&, chain](const ReasonFunction & reason) -> void {
                        if (logger)
                            emit_proof(chain, -1, reason);
                    };
                    inference.infer_less_than(logger, free_pos[i], target + 1_i,
                        JustifyExplicitlyThenRUP{justify}, generic_reason(state, rv));
                }
            };

            for (size_t a = 0; a < active_rects.size(); ++a) {
                auto i = active_rects[a];
                for (size_t b = a + 1; b < active_rects.size(); ++b) {
                    auto j = active_rects[b];
                    // Recompute fresh each pair: earlier pushes may have moved
                    // bounds this pass.
                    auto [lst_xi, eet_xi] = mand(xs[i], widths[i]);
                    auto [lst_yi, eet_yi] = mand(ys[i], heights[i]);
                    auto [lst_xj, eet_xj] = mand(xs[j], widths[j]);
                    auto [lst_yj, eet_yj] = mand(ys[j], heights[j]);
                    bool x_overlap = max(lst_xi, lst_xj) < min(eet_xi, eet_xj);
                    bool y_overlap = max(lst_yi, lst_yj) < min(eet_yi, eet_yj);
                    if (x_overlap) {
                        auto px = max(lst_xi, lst_xj);
                        push_axis(ys, heights, *bridge_y, before_y, *bridge_x, before_x, i, j, px);
                        push_axis(ys, heights, *bridge_y, before_y, *bridge_x, before_x, j, i, px);
                    }
                    if (y_overlap) {
                        auto py = max(lst_yi, lst_yj);
                        push_axis(xs, widths, *bridge_x, before_x, *bridge_y, before_y, i, j, py);
                        push_axis(xs, widths, *bridge_x, before_x, *bridge_y, before_y, j, i, py);
                    }
                }
            }

            // Strict-mode zero-area rectangles: the mandatory-box pass skips
            // them (their box is empty), but the declarative ≤-clause still
            // forbids a zero-area rectangle sitting inside another. Catch that
            // at an all-fixed leaf, where the encoded clause alone is RUP.
            // (Non-strict mode never has zero-area rects in active_rects.)
            auto zero_area = [&](size_t i) { return widths[i] == 0_i || heights[i] == 0_i; };
            auto fixed = [&](size_t i) {
                return state.has_single_value(xs[i]) && state.has_single_value(ys[i]);
            };
            for (size_t a = 0; a < active_rects.size(); ++a) {
                auto i = active_rects[a];
                if (! zero_area(i) || ! fixed(i))
                    continue;
                auto xi = state.lower_bound(xs[i]), yi = state.lower_bound(ys[i]);
                for (auto j : active_rects) {
                    if (j == i || ! fixed(j))
                        continue;
                    auto xj = state.lower_bound(xs[j]), yj = state.lower_bound(ys[j]);
                    bool sep = (xi + widths[i] <= xj) || (xj + widths[j] <= xi) ||
                        (yi + heights[i] <= yj) || (yj + heights[j] <= yi);
                    if (! sep) {
                        inference.contradiction(logger, JustifyUsingRUP{},
                            generic_reason(state, vector<IntegerVariableID>{xs[i], ys[i], xs[j], ys[j]}));
                        return PropagatorState::DisableUntilBacktrack;
                    }
                }
            }

            return PropagatorState::Enable;
        },
        triggers);
}

auto Disjunctive2D::s_exprify(const ProofModel * const model) const -> string
{
    stringstream s;
    print(s, "{} disjunctive2d{} (", _name, _strict ? "_strict" : "");
    for (const auto & v : _xs)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(v));
    print(s, " ) ( ");
    for (const auto & v : _ys)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(v));
    print(s, " ) ( ");
    for (const auto & w : _widths)
        print(s, " {}", w);
    print(s, " ) ( ");
    for (const auto & h : _heights)
        print(s, " {}", h);
    print(s, " )");
    return s.str();
}
