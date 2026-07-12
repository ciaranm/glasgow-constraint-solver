#include <gcs/constraints/disjunctive_2d/disjunctive_2d.hh>
#include <gcs/constraints/disjunctive_2d/hints.hh>
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
#include <map>
#include <memory>
#include <utility>
#include <variant>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::get;
using std::make_pair;
using std::make_unique;
using std::map;
using std::max;
using std::min;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::size_t;
using std::unique_ptr;
using std::vector;

namespace
{
    auto const_value_of(const IntegerVariableID & v) -> Integer
    {
        return get<ConstantIntegerVariableID>(v).const_value;
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

Disjunctive2D::Disjunctive2D(vector<IntegerVariableID> xs, vector<IntegerVariableID> ys, vector<IntegerVariableID> widths,
    vector<IntegerVariableID> heights) : _xs(move(xs)), _ys(move(ys)), _widths(move(widths)), _heights(move(heights))
{
    if (_xs.size() != _ys.size() || _xs.size() != _widths.size() || _xs.size() != _heights.size())
        throw InvalidProblemDefinitionException{"Disjunctive2D: xs, ys, widths, heights must have the same size"};
    // Constant non-negativity is checked here; variable sizes are checked in
    // prepare(), where their domains first become available.
    for (const auto & w : _widths)
        if (is_constant_variable(w) && const_value_of(w) < 0_i)
            throw InvalidProblemDefinitionException{"Disjunctive2D: widths must be non-negative"};
    for (const auto & h : _heights)
        if (is_constant_variable(h) && const_value_of(h) < 0_i)
            throw InvalidProblemDefinitionException{"Disjunctive2D: heights must be non-negative"};
}

Disjunctive2D::Disjunctive2D(vector<IntegerVariableID> xs, vector<IntegerVariableID> ys, vector<Integer> widths, vector<Integer> heights) :
    Disjunctive2D(move(xs), move(ys), as_constant_var_ids(widths), as_constant_var_ids(heights))
{
}

auto Disjunctive2D::with_strict(std::optional<bool> strict) -> Disjunctive2D &
{
    _strict = strict.value_or(true);
    return *this;
}

auto Disjunctive2D::clone() const -> unique_ptr<Constraint>
{
    auto cloned = make_unique<Disjunctive2D>(_xs, _ys, _widths, _heights);
    cloned->with_strict(_strict);
    return cloned;
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

    // Non-negativity: constant sizes are rejected in the constructor; variable
    // sizes are checked here, where their domains are finally available. A
    // negative size has no sensible rectangle interpretation, so treat it as a
    // modelling error rather than silently producing nonsense.
    for (size_t i = 0; i < n; ++i) {
        if (! is_constant_variable(_widths[i]) && initial_state.lower_bound(_widths[i]) < 0_i)
            throw InvalidProblemDefinitionException{"Disjunctive2D: widths must be non-negative"};
        if (! is_constant_variable(_heights[i]) && initial_state.lower_bound(_heights[i]) < 0_i)
            throw InvalidProblemDefinitionException{"Disjunctive2D: heights must be non-negative"};
    }

    // Resolve size snapshots. _*_vals is the constant value (0 placeholder for
    // a variable size); the initial upper bounds drive the active-rect filter.
    _width_vals.clear();
    _height_vals.clear();
    _width_vals.reserve(n);
    _height_vals.reserve(n);
    vector<Integer> width_ub, height_ub;
    width_ub.reserve(n);
    height_ub.reserve(n);
    for (size_t i = 0; i < n; ++i) {
        _width_vals.push_back(is_constant_variable(_widths[i]) ? const_value_of(_widths[i]) : 0_i);
        width_ub.push_back(initial_state.upper_bound(_widths[i]));
        _height_vals.push_back(is_constant_variable(_heights[i]) ? const_value_of(_heights[i]) : 0_i);
        height_ub.push_back(initial_state.upper_bound(_heights[i]));
    }

    // In non-strict mode, a rectangle whose width or height can only ever be 0
    // is zero-area and cannot overlap anything; drop it. In strict mode every
    // rectangle participates (its pairwise clauses remain in the OPB for leaf
    // correctness).
    _active_rects.reserve(n);
    for (size_t i = 0; i < n; ++i) {
        if (! _strict && (width_ub[i] == 0_i || height_ub[i] == 0_i))
            continue;
        _active_rects.push_back(i);
    }

    // Non-strict mode: a rectangle whose width or height is 0 does not
    // constrain, so every variable size gets a zero-size escape in the
    // separation clause -- matching cake_pb_cp, which adds the zw/zh disjunct
    // for every variable-size argument regardless of its bounds. Gating on
    // lower_bound == 0 changes the labelled separation row's content, and
    // proofs that pol-cite that label then fail to chain-verify (issue #482).
    // An always-positive size's escape is statically false and is refuted in
    // one RUP step where cited; the propagator already ignores zero-mandatory
    // rectangles via lb(size).
    _zero_escape_w.assign(n, false);
    _zero_escape_h.assign(n, false);
    if (! _strict)
        for (auto i : _active_rects) {
            _zero_escape_w[i] = ! is_constant_variable(_widths[i]);
            _zero_escape_h[i] = ! is_constant_variable(_heights[i]);
        }

    if (_active_rects.size() < 2)
        return false;

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
    // Nothing propagator-specific goes into the OPB, and (as in 1D
    // Disjunctive) this is also all the proof scaffolding there is: every
    // justification is a pol over these rows and order-literal definition
    // rows. A variable size stays on the flag's left-hand side and cancels
    // against its bound row in the same pol, so no proof-only end = pos + size
    // variable is needed.
    // before_{i,j} ⇔ pos_i + size_i ≤ pos_j. For a constant size this folds to
    // pos_i − pos_j ≤ −size (proof byte-identical to the constant-size case);
    // for a variable size the size term stays on the left.
    auto emit_before = [&](size_t idx_i, size_t idx_j, const std::string & axis_stem, IntegerVariableID pos_i, IntegerVariableID size_i,
                           Integer size_val_i, IntegerVariableID pos_j) -> BeforeFlagData {
        // cake_pb_cp names the "rectangle i precedes j on this axis" flag
        // x[id][i_j][bx] (x axis) / x[id][i_j][by] (y axis); match it.
        auto flag =
            model.create_proof_flag(_constraint_id, vector<long long>{static_cast<long long>(idx_i), static_cast<long long>(idx_j)}, axis_stem);
        auto ineq = is_constant_variable(size_i) ? (WPBSum{} + 1_i * pos_i + -1_i * pos_j <= -size_val_i)
                                                 : (WPBSum{} + 1_i * pos_i + 1_i * size_i + -1_i * pos_j <= 0_i);
        auto [fwd, rev] = model.add_two_way_reified_constraint(ineq, flag);
        return BeforeFlagData{flag, fwd, rev};
    };

    // Non-strict mode: a zero-size escape flag per size that can be 0.
    _zero_w.assign(_xs.size(), nullopt);
    _zero_h.assign(_xs.size(), nullopt);
    for (auto i : _active_rects) {
        // cake_pb_cp names the zero-size escapes x[id][i][zw] / x[id][i][zh].
        if (_zero_escape_w[i])
            _zero_w[i] = model.create_proof_flag_fully_reifying(
                _constraint_id, vector<long long>{static_cast<long long>(i)}, "zw", WPBSum{} + 1_i * _widths[i] <= 0_i);
        if (_zero_escape_h[i])
            _zero_h[i] = model.create_proof_flag_fully_reifying(
                _constraint_id, vector<long long>{static_cast<long long>(i)}, "zh", WPBSum{} + 1_i * _heights[i] <= 0_i);
    }

    for (size_t a = 0; a < _active_rects.size(); ++a) {
        auto i = _active_rects[a];
        for (size_t b = a + 1; b < _active_rects.size(); ++b) {
            auto j = _active_rects[b];
            auto bx_ij = emit_before(i, j, "bx", _xs[i], _widths[i], _width_vals[i], _xs[j]);
            auto bx_ji = emit_before(j, i, "bx", _xs[j], _widths[j], _width_vals[j], _xs[i]);
            auto by_ij = emit_before(i, j, "by", _ys[i], _heights[i], _height_vals[i], _ys[j]);
            auto by_ji = emit_before(j, i, "by", _ys[j], _heights[j], _height_vals[j], _ys[i]);
            // A zero-area rectangle escapes the separation clause.
            auto clause_sum = WPBSum{} + 1_i * bx_ij.flag + 1_i * bx_ji.flag + 1_i * by_ij.flag + 1_i * by_ji.flag;
            for (auto r : {i, j}) {
                if (_zero_w[r])
                    clause_sum += 1_i * *_zero_w[r];
                if (_zero_h[r])
                    clause_sum += 1_i * *_zero_h[r];
            }
            // cake_pb_cp labels the separation clause @c[id][<i>_<j>sepal1].
            auto clause =
                model.add_labelled_constraint(_constraint_id, std::to_string(i) + "_" + std::to_string(j) + "sepal1", move(clause_sum) >= 1_i);
            _before_x.emplace(make_pair(i, j), bx_ij);
            _before_x.emplace(make_pair(j, i), bx_ji);
            _before_y.emplace(make_pair(i, j), by_ij);
            _before_y.emplace(make_pair(j, i), by_ji);
            _clause_lines.emplace(make_pair(i, j), clause);
        }
    }
}

auto Disjunctive2D::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    for (auto i : _active_rects) {
        triggers.on_bounds.emplace_back(_xs[i]);
        triggers.on_bounds.emplace_back(_ys[i]);
        // A rise in a rectangle's minimum size extends its mandatory part, so
        // re-fire on variable-size bound changes too.
        if (! is_constant_variable(_widths[i]))
            triggers.on_bounds.emplace_back(_widths[i]);
        if (! is_constant_variable(_heights[i]))
            triggers.on_bounds.emplace_back(_heights[i]);
    }

    propagators.install(
        constraint_id(),
        [xs = move(_xs), ys = move(_ys), width_var = move(_widths), height_var = move(_heights), active_rects = move(_active_rects),
            before_x = move(_before_x), before_y = move(_before_y), clause_lines = move(_clause_lines), zero_w = move(_zero_w),
            zero_h = move(_zero_h), strict = _strict,
            owner = constraint_id()](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // Pairwise 2D time-table. The mandatory box of rectangle i is
            //   [ub(x_i), lb(x_i)+lb(w_i)) x [ub(y_i), lb(y_i)+lb(h_i))
            // -- the cells it must occupy regardless of where it is placed (a
            // variable size uses its minimum). Two rectangles whose mandatory
            // boxes overlap on both axes is infeasible.
            auto wlb = [&](size_t i) { return state.lower_bound(width_var[i]); };
            auto hlb = [&](size_t i) { return state.lower_bound(height_var[i]); };
            auto w_is_var = [&](size_t i) { return ! is_constant_variable(width_var[i]); };
            auto h_is_var = [&](size_t i) { return ! is_constant_variable(height_var[i]); };

            // The pairwise proof vocabulary, exactly as in 1D Disjunctive: a
            // pol over a before flag's [r] row (flag -> pos_a + size_a <=
            // pos_b) plus one bound-literal definition row per operand
            // cancels the integer terms exactly, leaving a clause over the
            // flag's negation and the residual order literals, which the
            // closing reason-wrapped RUPs then unit-propagate. The pol is
            // load-bearing; see dev_docs/disjunctive-proof-logging.md.
            auto emit_before_pol = [&](const map<pair<size_t, size_t>, BeforeFlagData> & before, const vector<IntegerVariableID> & size, size_t a,
                                       size_t b, const optional<IntegerVariableCondition> & cond_a,
                                       const optional<IntegerVariableCondition> & cond_b) -> void {
                auto & tracker = logger->names_and_ids_tracker();
                PolBuilder pol;
                pol.add(before.at(make_pair(a, b)).forward_line);
                // As in 1D: add cond's order-literal definition row, but a
                // literal that maps directly onto one encoding bit has no
                // definition row and nothing to add -- the operand's term
                // already normalises to exactly that residual literal.
                auto add_defining_row = [&](const IntegerVariableCondition & cond) -> void {
                    auto item = tracker.need_pol_item_defining_literal(cond);
                    if (auto * line = std::get_if<ProofLine>(&item))
                        pol.add(*line);
                };
                if (cond_a)
                    add_defining_row(*cond_a);
                if (! is_constant_variable(size[a]))
                    add_defining_row(size[a] >= state.lower_bound(size[a]));
                if (cond_b)
                    add_defining_row(*cond_b);
                pol.saturate().emit(*logger, ProofLevel::Temporary);
            };

            // The current-bound literals on a position, or nullopt for a
            // constant (a constant has no defining literal to cite).
            auto lb_lit = [&](const IntegerVariableID & v) -> optional<IntegerVariableCondition> {
                if (is_constant_variable(v))
                    return nullopt;
                return v >= state.lower_bound(v);
            };
            auto ub_lit = [&](const IntegerVariableID & v) -> optional<IntegerVariableCondition> {
                if (is_constant_variable(v))
                    return nullopt;
                return v < state.upper_bound(v) + 1_i;
            };

            // Non-strict mode: a rectangle that can be zero-area carries a
            // size<=0 escape flag in its clauses. Whenever an inference fires
            // the relevant sizes are >= 1, so pin those flags false (RUP
            // under reason) so the separation clause reduces to its
            // before-flag disjunction. No-op in strict mode / for
            // always-positive sizes.
            auto pin_escapes = [&](const ReasonLiterals & reason, size_t i, size_t j) -> void {
                for (auto r : {i, j}) {
                    if (zero_w[r])
                        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * *zero_w[r] <= 0_i, ProofLevel::Temporary);
                    if (zero_h[r])
                        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * *zero_h[r] <= 0_i, ProofLevel::Temporary);
                }
            };

            auto mand = [&](IntegerVariableID pos, Integer size) -> pair<Integer, Integer> {
                return {state.upper_bound(pos), state.lower_bound(pos) + size};
            };

            for (size_t a = 0; a < active_rects.size(); ++a) {
                auto i = active_rects[a];
                auto [lst_xi, eet_xi] = mand(xs[i], wlb(i));
                auto [lst_yi, eet_yi] = mand(ys[i], hlb(i));
                if (lst_xi >= eet_xi || lst_yi >= eet_yi)
                    continue;
                for (size_t b = a + 1; b < active_rects.size(); ++b) {
                    auto j = active_rects[b];
                    auto [lst_xj, eet_xj] = mand(xs[j], wlb(j));
                    auto [lst_yj, eet_yj] = mand(ys[j], hlb(j));
                    if (lst_xj >= eet_xj || lst_yj >= eet_yj)
                        continue;
                    auto x_overlap = max(lst_xi, lst_xj) < min(eet_xi, eet_xj);
                    auto y_overlap = max(lst_yi, lst_yj) < min(eet_yi, eet_yj);
                    if (x_overlap && y_overlap) {
                        auto justify = [&, i, j](const ReasonLiterals & reason) -> void {
                            pin_escapes(reason, i, j);
                            // The mandatory boxes overlap on both axes, so no
                            // separating direction is available: for each axis
                            // and direction, the before flag's [r] row plus
                            // the mandatory bounds (lb of the preceder's
                            // position and size, ub of the other's position)
                            // is infeasible, so four pols force all four flags
                            // false under the reason and the 4-way separation
                            // clause unit-fails in the framework's closing
                            // reason-wrapped RUP.
                            emit_before_pol(before_x, width_var, i, j, lb_lit(xs[i]), ub_lit(xs[j]));
                            emit_before_pol(before_x, width_var, j, i, lb_lit(xs[j]), ub_lit(xs[i]));
                            emit_before_pol(before_y, height_var, i, j, lb_lit(ys[i]), ub_lit(ys[j]));
                            emit_before_pol(before_y, height_var, j, i, lb_lit(ys[j]), ub_lit(ys[i]));
                        };

                        vector<IntegerVariableID> rvars{xs[i], ys[i], xs[j], ys[j]};
                        for (auto r : {i, j}) {
                            if (w_is_var(r))
                                rvars.push_back(width_var[r]);
                            if (h_is_var(r))
                                rvars.push_back(height_var[r]);
                        }
                        inference.contradiction(logger, JustifyExplicitly{justify, ThenRUP::Yes, hints::Disjunctive2D{owner}}, generic_reason(rvars));
                        return PropagatorState::DisableUntilBacktrack;
                    }
                }
            }

            // Pairwise bound pushes. A pair whose mandatory parts overlap on one
            // axis (the "forced" axis) must separate on the other (the "free"
            // axis) -- no pair overlaps on both, since the contradiction pass
            // returned otherwise. So the pushed rectangle is moved clear of the
            // blocker's mandatory part on the free axis: a 1D single-blocker
            // disjunctive push. The justification is six pols: two eliminate
            // the forced-axis precedences (both refuted by the mandatory
            // overlap), and the free-axis dichotomy is the 1D chain step --
            // the impossible free direction refuted from the pushed bound, the
            // surviving direction folded onto the target order literal's
            // definition row -- so with the escapes pinned the 4-way clause
            // forces the target in the framework's closing RUP. One step
            // regardless of the blocker's size.
            //
            // free_is_x selects which axis we push on (the other is the forced
            // axis they overlap on). i is pushed, j blocks.
            auto push_axis = [&](bool free_is_x, size_t i, size_t j) {
                const auto & free_pos = free_is_x ? xs : ys;
                const auto & free_size = free_is_x ? width_var : height_var;
                const auto & free_before = free_is_x ? before_x : before_y;
                const auto & forced_pos = free_is_x ? ys : xs;
                const auto & forced_size = free_is_x ? height_var : width_var;
                const auto & forced_before = free_is_x ? before_y : before_x;

                auto sz = state.lower_bound(free_size[i]);
                if (sz == 0_i)
                    return; // a zero-size rectangle spans no cells on this axis
                auto [cur_lo, cur_hi] = state.bounds(free_pos[i]);
                auto blk_lo = state.upper_bound(free_pos[j]);
                auto blk_hi = state.lower_bound(free_pos[j]) + state.lower_bound(free_size[j]);
                if (blk_lo >= blk_hi)
                    return; // blocker has no mandatory part on the free axis

                vector<IntegerVariableID> rv{xs[i], ys[i], xs[j], ys[j]};
                for (auto r : {i, j}) {
                    if (w_is_var(r))
                        rv.push_back(width_var[r]);
                    if (h_is_var(r))
                        rv.push_back(height_var[r]);
                }

                // Both forced-axis precedences are refuted by the mandatory
                // overlap on that axis, exactly as in the contradiction.
                auto eliminate_forced_axis = [&]() -> void {
                    emit_before_pol(forced_before, forced_size, i, j, lb_lit(forced_pos[i]), ub_lit(forced_pos[j]));
                    emit_before_pol(forced_before, forced_size, j, i, lb_lit(forced_pos[j]), ub_lit(forced_pos[i]));
                };

                // lb-push: i cannot fit below the blocker, push its origin up to
                // blk_hi -- capped at cur_hi + 1 (beyond that the domain is
                // empty).
                if (cur_lo > blk_lo - sz && cur_lo < blk_hi) {
                    auto target = min(blk_hi, cur_hi + 1_i);
                    // The pushed position's own bound literal is passed
                    // explicitly (cur_lo, captured): the inference has already
                    // landed by the time the justification runs, so re-reading
                    // the pushed variable's bounds from the state would cite
                    // the post-push bound, which the reason does not support.
                    auto justify = [&, i, j, cur_lo = cur_lo, target](const ReasonLiterals & reason) -> void {
                        pin_escapes(reason, i, j);
                        eliminate_forced_axis();
                        // Free axis: i entirely before j contradicts i's lower
                        // bound (it cannot fit below the blocker) ...
                        emit_before_pol(free_before, free_size, i, j, free_pos[i] >= cur_lo, ub_lit(free_pos[j]));
                        // ... so j precedes i, putting pos_i at j's mandatory
                        // end or later, folded onto the target order literal's
                        // definition row: bf -> pos_i >= target.
                        emit_before_pol(free_before, free_size, j, i, lb_lit(free_pos[j]), free_pos[i] < target);
                    };
                    inference.infer_greater_than_or_equal(
                        logger, free_pos[i], target, JustifyExplicitly{justify, ThenRUP::Yes, hints::Disjunctive2D{owner}}, generic_reason(rv));
                }
                // ub-push: i cannot fit above the blocker, push its origin down to
                // blk_lo - sz -- capped at cur_lo - 1 by the same reasoning.
                else if (cur_hi > blk_lo - sz && cur_hi < blk_hi) {
                    auto target = max(blk_lo - sz, cur_lo - 1_i);
                    // As above: cur_hi is captured, not re-read, because the
                    // push has landed by justification time.
                    auto justify = [&, i, j, cur_hi = cur_hi, target](const ReasonLiterals & reason) -> void {
                        pin_escapes(reason, i, j);
                        eliminate_forced_axis();
                        // Free axis: j entirely before i would put pos_i past
                        // its upper bound (i cannot fit above the blocker) ...
                        emit_before_pol(free_before, free_size, j, i, lb_lit(free_pos[j]), free_pos[i] < cur_hi + 1_i);
                        // ... so i precedes j, capping pos_i at the blocker's
                        // latest start minus lb(size_i), folded onto the
                        // target: bf -> pos_i <= target.
                        emit_before_pol(free_before, free_size, i, j, free_pos[i] >= target + 1_i, ub_lit(free_pos[j]));
                    };
                    inference.infer_less_than(
                        logger, free_pos[i], target + 1_i, JustifyExplicitly{justify, ThenRUP::Yes, hints::Disjunctive2D{owner}}, generic_reason(rv));
                }
            };

            for (size_t a = 0; a < active_rects.size(); ++a) {
                auto i = active_rects[a];
                for (size_t b = a + 1; b < active_rects.size(); ++b) {
                    auto j = active_rects[b];
                    // Recompute fresh each pair: earlier pushes may have moved
                    // bounds this pass.
                    auto [lst_xi, eet_xi] = mand(xs[i], wlb(i));
                    auto [lst_yi, eet_yi] = mand(ys[i], hlb(i));
                    auto [lst_xj, eet_xj] = mand(xs[j], wlb(j));
                    auto [lst_yj, eet_yj] = mand(ys[j], hlb(j));
                    bool x_overlap = max(lst_xi, lst_xj) < min(eet_xi, eet_xj);
                    bool y_overlap = max(lst_yi, lst_yj) < min(eet_yi, eet_yj);
                    if (x_overlap) {
                        push_axis(false, i, j); // free axis = y
                        push_axis(false, j, i);
                    }
                    if (y_overlap) {
                        push_axis(true, i, j); // free axis = x
                        push_axis(true, j, i);
                    }
                }
            }

            // Strict-mode zero-area rectangles: the mandatory-box pass skips
            // them (their box is empty), but the declarative ≤-clause still
            // forbids a zero-area rectangle sitting inside another. Catch that
            // at an all-fixed leaf, where the encoded clause alone is RUP.
            // (Non-strict mode never has zero-area rects in active_rects.)
            // (Only meaningful in strict mode; non-strict zero-area rectangles
            // do not constrain anything, so they are never checked here.)
            auto zero_area = [&](size_t i) { return strict && (wlb(i) == 0_i || hlb(i) == 0_i); };
            auto fixed = [&](size_t i) {
                return state.has_single_value(xs[i]) && state.has_single_value(ys[i]) && state.has_single_value(width_var[i]) &&
                    state.has_single_value(height_var[i]);
            };
            for (size_t a = 0; a < active_rects.size(); ++a) {
                auto i = active_rects[a];
                if (! fixed(i) || ! zero_area(i))
                    continue;
                auto xi = state.lower_bound(xs[i]), yi = state.lower_bound(ys[i]);
                for (auto j : active_rects) {
                    if (j == i || ! fixed(j))
                        continue;
                    auto xj = state.lower_bound(xs[j]), yj = state.lower_bound(ys[j]);
                    bool sep = (xi + wlb(i) <= xj) || (xj + wlb(j) <= xi) || (yi + hlb(i) <= yj) || (yj + hlb(j) <= yi);
                    if (! sep) {
                        vector<IntegerVariableID> lr{xs[i], ys[i], xs[j], ys[j]};
                        for (auto r : {i, j}) {
                            if (w_is_var(r))
                                lr.push_back(width_var[r]);
                            if (h_is_var(r))
                                lr.push_back(height_var[r]);
                        }
                        inference.contradiction(logger, JustifyUsingRUP{hints::Disjunctive2D{owner}}, generic_reason(lr));
                        return PropagatorState::DisableUntilBacktrack;
                    }
                }
            }

            return PropagatorState::Enable;
        },
        triggers);
}

auto Disjunctive2D::constraint_type() const -> std::string
{
    return _strict ? "disjunctive2d_strict" : "disjunctive2d";
}

auto Disjunctive2D::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    vector<SExpr> xs, ys, widths, heights;
    for (const auto & v : _xs)
        xs.push_back(tracker.s_expr_term_of(v));
    for (const auto & v : _ys)
        ys.push_back(tracker.s_expr_term_of(v));
    for (const auto & w : _widths)
        widths.push_back(tracker.s_expr_term_of(w));
    for (const auto & h : _heights)
        heights.push_back(tracker.s_expr_term_of(h));
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(std::move(xs)),
        SExpr::list(std::move(ys)), SExpr::list(std::move(widths)), SExpr::list(std::move(heights))});
}
