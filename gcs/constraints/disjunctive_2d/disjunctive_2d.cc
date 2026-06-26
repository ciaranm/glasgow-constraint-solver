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
using std::get;
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
    vector<IntegerVariableID> heights, bool strict) : _xs(move(xs)), _ys(move(ys)), _widths(move(widths)), _heights(move(heights)), _strict(strict)
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

Disjunctive2D::Disjunctive2D(vector<IntegerVariableID> xs, vector<IntegerVariableID> ys, vector<Integer> widths, vector<Integer> heights,
    bool strict) : Disjunctive2D(move(xs), move(ys), as_constant_var_ids(widths), as_constant_var_ids(heights), strict)
{
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

    // Resolve size snapshots. _*_vals is the constant value (0 placeholder for a
    // variable size); _*_ub is the initial upper bound.
    _width_vals.clear();
    _width_ub.clear();
    _height_vals.clear();
    _height_ub.clear();
    _width_vals.reserve(n);
    _width_ub.reserve(n);
    _height_vals.reserve(n);
    _height_ub.reserve(n);
    for (size_t i = 0; i < n; ++i) {
        _width_vals.push_back(is_constant_variable(_widths[i]) ? const_value_of(_widths[i]) : 0_i);
        _width_ub.push_back(initial_state.upper_bound(_widths[i]));
        _height_vals.push_back(is_constant_variable(_heights[i]) ? const_value_of(_heights[i]) : 0_i);
        _height_ub.push_back(initial_state.upper_bound(_heights[i]));
    }

    // In non-strict mode, a rectangle whose width or height can only ever be 0
    // is zero-area and cannot overlap anything; drop it. In strict mode every
    // rectangle participates (its pairwise clauses remain in the OPB for leaf
    // correctness).
    _active_rects.reserve(n);
    for (size_t i = 0; i < n; ++i) {
        if (! _strict && (_width_ub[i] == 0_i || _height_ub[i] == 0_i))
            continue;
        _active_rects.push_back(i);
    }

    // Non-strict mode: a rectangle whose width or height can be 0 may be
    // zero-area for some assignments, in which case it does not constrain. Note
    // which sizes can be zero so define_proof_model can add a zero-size escape
    // to the separation clause; the propagator already ignores zero-mandatory
    // rectangles via lb(size).
    _can_be_zero_w.assign(n, false);
    _can_be_zero_h.assign(n, false);
    if (! _strict)
        for (auto i : _active_rects) {
            _can_be_zero_w[i] = ! is_constant_variable(_widths[i]) && initial_state.lower_bound(_widths[i]) == 0_i;
            _can_be_zero_h[i] = ! is_constant_variable(_heights[i]) && initial_state.lower_bound(_heights[i]) == 0_i;
        }

    if (_active_rects.size() < 2)
        return false;

    // Possible-active windows use the largest possible size.
    _x_lo.assign(n, 0_i);
    _x_hi.assign(n, 0_i);
    _y_lo.assign(n, 0_i);
    _y_hi.assign(n, 0_i);
    for (auto i : _active_rects) {
        auto [x_lo, x_hi] = initial_state.bounds(_xs[i]);
        auto [y_lo, y_hi] = initial_state.bounds(_ys[i]);
        _x_lo[i] = x_lo;
        _x_hi[i] = x_hi + _width_ub[i] - 1_i;
        _y_lo[i] = y_lo;
        _y_hi[i] = y_hi + _height_ub[i] - 1_i;
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
        auto [fwd, rev] = model.add_two_way_reified_constraint("Disjunctive2D", "first rectangle precedes second on this axis", ineq, flag);
        return BeforeFlagData{flag, fwd, rev};
    };

    // For each rectangle with a variable size on an axis, a proof-only
    // end = pos + size with both definition directions captured.
    _end_x.assign(_xs.size(), nullopt);
    _end_y.assign(_xs.size(), nullopt);
    _end_x_ge.assign(_xs.size(), nullopt);
    _end_x_le.assign(_xs.size(), nullopt);
    _end_y_ge.assign(_xs.size(), nullopt);
    _end_y_le.assign(_xs.size(), nullopt);
    auto make_end = [&](IntegerVariableID pos, IntegerVariableID size, Integer dom_hi, optional<ProofOnlySimpleIntegerVariableID> & end_out,
                        optional<ProofLine> & ge_out, optional<ProofLine> & le_out) {
        auto end = model.create_proof_only_integer_variable(0_i, dom_hi, "d2dend", IntegerVariableProofRepresentation::Bits);
        ge_out = model.add_constraint("Disjunctive2D", "end >= pos + size", WPBSum{} + 1_i * end + -1_i * pos + -1_i * size >= 0_i);
        le_out = model.add_constraint("Disjunctive2D", "end <= pos + size", WPBSum{} + 1_i * end + -1_i * pos + -1_i * size <= 0_i);
        end_out = end;
    };
    for (auto i : _active_rects) {
        if (! is_constant_variable(_widths[i]))
            make_end(_xs[i], _widths[i], _x_hi[i] + 1_i, _end_x[i], _end_x_ge[i], _end_x_le[i]);
        if (! is_constant_variable(_heights[i]))
            make_end(_ys[i], _heights[i], _y_hi[i] + 1_i, _end_y[i], _end_y_ge[i], _end_y_le[i]);
    }

    // Non-strict mode: a zero-size escape flag per size that can be 0.
    _zero_w.assign(_xs.size(), nullopt);
    _zero_h.assign(_xs.size(), nullopt);
    for (auto i : _active_rects) {
        // cake_pb_cp names the zero-size escapes x[id][i][zw] / x[id][i][zh].
        if (_can_be_zero_w[i])
            _zero_w[i] = model.create_proof_flag_fully_reifying(
                _constraint_id, vector<long long>{static_cast<long long>(i)}, "zw", WPBSum{} + 1_i * _widths[i] <= 0_i);
        if (_can_be_zero_h[i])
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
            auto clause = model.add_constraint("Disjunctive2D", "rectangles must be separated on some axis", move(clause_sum) >= 1_i);
            _before_x.emplace(make_pair(i, j), bx_ij);
            _before_x.emplace(make_pair(j, i), bx_ji);
            _before_y.emplace(make_pair(i, j), by_ij);
            _before_y.emplace(make_pair(j, i), by_ji);
            _clause_lines.emplace(make_pair(i, j), clause);
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
        [xs = _xs, ys = _ys, width_var = _widths, height_var = _heights, widths = _width_vals, heights = _height_vals, width_ub = _width_ub,
            height_ub = _height_ub, end_x = _end_x, end_y = _end_y, active_rects = _active_rects, x_lo = _x_lo, x_hi = _x_hi, y_lo = _y_lo,
            y_hi = _y_hi, bridge_x, bridge_y](State &, auto &, ProofLogger * const logger) -> void {
            if (! logger || logger->get_assertion_level() > AssertionLevel::Off)
                return;
            // "after" reifies on pos + size >= t+1; for a constant size that is
            // the single-variable pos >= t-size+1, for a variable size the
            // single-variable end >= t+1 (end = pos + size).
            auto emit_axis = [&](BridgeMap & bridge, const vector<IntegerVariableID> & pos, const vector<IntegerVariableID> & size_var,
                                 const vector<Integer> & size_val, const vector<optional<ProofOnlySimpleIntegerVariableID>> & end, size_t i,
                                 Integer lo, Integer hi) {
                for (Integer t = lo; t <= hi; ++t) {
                    auto [B, B_fwd, B_rev] = logger->create_proof_flag_reifying(WPBSum{} + 1_i * pos[i] <= t, "d2dbef", ProofLevel::Top);
                    auto [F, F_fwd, F_rev] = is_constant_variable(size_var[i])
                        ? logger->create_proof_flag_reifying(WPBSum{} + 1_i * pos[i] >= t - size_val[i] + 1_i, "d2daft", ProofLevel::Top)
                        : logger->create_proof_flag_reifying(WPBSum{} + 1_i * *end[i] >= t + 1_i, "d2daft", ProofLevel::Top);
                    auto [A, A_fwd, A_rev] = logger->create_proof_flag_reifying(WPBSum{} + 1_i * B + 1_i * F >= 2_i, "d2dact", ProofLevel::Top);
                    bridge.emplace(make_pair(i, t), BridgeFlags{B, B_fwd, B_rev, F, F_fwd, F_rev, A, A_fwd, A_rev});
                }
            };
            for (auto i : active_rects) {
                if (width_ub[i] > 0_i)
                    emit_axis(*bridge_x, xs, width_var, widths, end_x, i, x_lo[i], x_hi[i]);
                if (height_ub[i] > 0_i)
                    emit_axis(*bridge_y, ys, height_var, heights, end_y, i, y_lo[i], y_hi[i]);
            }
        });

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
            before_x = move(_before_x), before_y = move(_before_y), clause_lines = move(_clause_lines), end_x = move(_end_x), end_y = move(_end_y),
            end_x_ge = move(_end_x_ge), end_x_le = move(_end_x_le), end_y_ge = move(_end_y_ge), end_y_le = move(_end_y_le), zero_w = move(_zero_w),
            zero_h = move(_zero_h), strict = _strict, owner = constraint_id(), bridge_x,
            bridge_y](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // Pairwise 2D time-table. The mandatory box of rectangle i is
            //   [ub(x_i), lb(x_i)+lb(w_i)) x [ub(y_i), lb(y_i)+lb(h_i))
            // -- the cells it must occupy regardless of where it is placed (a
            // variable size uses its minimum). Two rectangles whose mandatory
            // boxes overlap on both axes is infeasible.
            auto wlb = [&](size_t i) { return state.lower_bound(width_var[i]); };
            auto hlb = [&](size_t i) { return state.lower_bound(height_var[i]); };
            auto w_is_var = [&](size_t i) { return ! is_constant_variable(width_var[i]); };
            auto h_is_var = [&](size_t i) { return ! is_constant_variable(height_var[i]); };

            // Non-strict mode: a rectangle that can be zero-area carries a
            // size<=0 escape flag in its clauses. Whenever an inference fires the
            // relevant sizes are >= 1, so pin those flags false (RUP) and add the
            // lines to the clause pol so it reduces to the before-flag
            // disjunction. No-op in strict mode / for always-positive sizes.
            auto add_escape_pins = [&](PolBuilder & pol, const ReasonLiterals & reason, size_t i, size_t j) {
                for (auto r : {i, j}) {
                    if (zero_w[r])
                        pol.add(logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * *zero_w[r] <= 0_i, ProofLevel::Temporary));
                    if (zero_h[r])
                        pol.add(logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * *zero_h[r] <= 0_i, ProofLevel::Temporary));
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
                        // Pick a cell (p, q) inside both mandatory boxes.
                        auto p = max(lst_xi, lst_xj);
                        auto q = max(lst_yi, lst_yj);

                        auto justify = [&, i, j, p, q](const ReasonLiterals & reason) -> void {
                            // Pin "rect r spans coord on this axis" = 1 under the
                            // bounds reason: before, then after, then active (UP
                            // can't chase active's AND-gate in one step). For a
                            // variable size the "after" reifies on end = pos+size;
                            // materialise end >= lb(pos)+lb(size) first so the
                            // after RUP closes single-variable in end (the
                            // Cumulative end-proxy technique).
                            auto pin = [&](BridgeMap & bridge, const optional<ProofOnlySimpleIntegerVariableID> & end_opt,
                                           const optional<ProofLine> & end_ge, IntegerVariableID pos, IntegerVariableID size, Integer coord,
                                           size_t r) -> ProofLine {
                                auto & bf = bridge.at(make_pair(r, coord));
                                logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * bf.before >= 1_i, ProofLevel::Temporary);
                                if (end_opt)
                                    PolBuilder{}
                                        .add(*end_ge)
                                        .add_for_literal(logger->names_and_ids_tracker(), pos >= state.lower_bound(pos))
                                        .add_for_literal(logger->names_and_ids_tracker(), size >= state.lower_bound(size))
                                        .emit(*logger, ProofLevel::Temporary);
                                logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * bf.after >= 1_i, ProofLevel::Temporary);
                                return logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * bf.active >= 1_i, ProofLevel::Temporary);
                            };
                            auto Ax_i = pin(*bridge_x, end_x[i], end_x_ge[i], xs[i], width_var[i], p, i);
                            auto Ay_i = pin(*bridge_y, end_y[i], end_y_ge[i], ys[i], height_var[i], q, i);
                            auto Ax_j = pin(*bridge_x, end_x[j], end_x_ge[j], xs[j], width_var[j], p, j);
                            auto Ay_j = pin(*bridge_y, end_y[j], end_y_ge[j], ys[j], height_var[j], q, j);

                            auto & bx_i = bridge_x->at(make_pair(i, p));
                            auto & bx_j = bridge_x->at(make_pair(j, p));
                            auto & by_i = bridge_y->at(make_pair(i, q));
                            auto & by_j = bridge_y->at(make_pair(j, q));

                            // For each axis/direction, derive "the precedence
                            // flag is false given both rects span the cell": the
                            // integer terms cancel (cf. 1D Disjunctive pair_ne).
                            // For a variable "after"-rect size, the end <= pos+size
                            // line cancels end back to pos+size so it cancels the
                            // before flag's pos+size term.
                            auto Lpol = [&](const BeforeFlagData & bf_ab, const BridgeFlags & aft_a, const BridgeFlags & bef_b,
                                            const optional<ProofLine> & aft_end_le) -> ProofLine {
                                PolBuilder pol;
                                pol.add(bf_ab.forward_line).add(aft_a.after_fwd).add(bef_b.before_fwd);
                                if (aft_end_le)
                                    pol.add(*aft_end_le);
                                return pol.saturate().emit(*logger, ProofLevel::Temporary);
                            };
                            auto Lx1 = Lpol(before_x.at(make_pair(i, j)), bx_i, bx_j, end_x_le[i]);
                            auto Lx2 = Lpol(before_x.at(make_pair(j, i)), bx_j, bx_i, end_x_le[j]);
                            auto Ly1 = Lpol(before_y.at(make_pair(i, j)), by_i, by_j, end_y_le[i]);
                            auto Ly2 = Lpol(before_y.at(make_pair(j, i)), by_j, by_i, end_y_le[j]);

                            // Combine the four precedence-false lines with the
                            // 4-way separation clause and the four active AND-gate
                            // forward reifs: the precedence and before/after terms
                            // cancel, leaving "not all four spans hold". Pin any
                            // zero-size escape flags false first (non-strict).
                            PolBuilder nb;
                            nb.add(clause_lines.at(make_pair(min(i, j), max(i, j))))
                                .add(Lx1)
                                .add(Lx2)
                                .add(Ly1)
                                .add(Ly2)
                                .add(bx_i.active_fwd)
                                .add(bx_j.active_fwd)
                                .add(by_i.active_fwd)
                                .add(by_j.active_fwd);
                            add_escape_pins(nb, reason, i, j);
                            auto not_all = nb.saturate().emit(*logger, ProofLevel::Temporary);

                            // Pol "not all four spans" against the four pinned
                            // spans: infeasible under the reason, closing the
                            // framework's wrapping RUP.
                            PolBuilder{}.add(not_all).add(Ax_i).add(Ay_i).add(Ax_j).add(Ay_j).emit(*logger, ProofLevel::Temporary);
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
            // disjunctive push, justified by deriving the reduced clause
            // by_ij + by_ji >= 1 from the forced-axis overlap and then running a
            // 1D-style chain against it on the free axis.
            //
            // free_*: the axis we push on; forced_*: the axis they overlap on;
            // i is pushed, j blocks, forced_col is a column both span on the
            // forced axis.
            // free_is_x selects which axis we push on (the other is the forced
            // axis they overlap on). i is pushed, j blocks, forced_col is a
            // column both span on the forced axis. Variable sizes get the
            // Cumulative end-proxy treatment throughout: the "after" pin
            // materialises end's bound, and the before-flag pol cancels end back
            // to pos+size.
            struct ChainStep
            {
                Integer t;
                // Start bound that, with lb(size), forces the pushed rect to span
                // t: the running bound for lb-push, t−sz+1 for ub-push.
                Integer s_lo;
            };
            auto push_axis = [&](bool free_is_x, size_t i, size_t j, Integer forced_col) {
                const auto & free_pos = free_is_x ? xs : ys;
                const auto & free_size = free_is_x ? width_var : height_var;
                const auto & free_end = free_is_x ? end_x : end_y;
                const auto & free_end_ge = free_is_x ? end_x_ge : end_y_ge;
                const auto & free_end_le = free_is_x ? end_x_le : end_y_le;
                auto & free_bridge = free_is_x ? *bridge_x : *bridge_y;
                const auto & free_before = free_is_x ? before_x : before_y;
                const auto & forced_pos = free_is_x ? ys : xs;
                const auto & forced_size = free_is_x ? height_var : width_var;
                const auto & forced_end = free_is_x ? end_y : end_x;
                const auto & forced_end_ge = free_is_x ? end_y_ge : end_x_ge;
                const auto & forced_end_le = free_is_x ? end_y_le : end_x_le;
                auto & forced_bridge = free_is_x ? *bridge_y : *bridge_x;
                const auto & forced_before = free_is_x ? before_y : before_x;

                auto sz = state.lower_bound(free_size[i]);
                if (sz == 0_i)
                    return; // a zero-size rectangle spans no cells on this axis
                auto [cur_lo, cur_hi] = state.bounds(free_pos[i]);
                auto blk_lo = state.upper_bound(free_pos[j]);
                auto blk_hi = state.lower_bound(free_pos[j]) + state.lower_bound(free_size[j]);
                if (blk_lo >= blk_hi)
                    return; // blocker has no mandatory part on the free axis
                auto is_blocked = [&](Integer t) { return t >= blk_lo && t < blk_hi; };

                vector<IntegerVariableID> rv{xs[i], ys[i], xs[j], ys[j]};
                for (auto r : {i, j}) {
                    if (w_is_var(r))
                        rv.push_back(width_var[r]);
                    if (h_is_var(r))
                        rv.push_back(height_var[r]);
                }

                // Emit the reduced clause by_ij + by_ji >= 1 (forced-axis
                // elimination), then one chain step per blocked free-cell. dir
                // = +1 for an lb-push (ext_lit: pos > t), -1 for a ub-push.
                auto emit_proof = [&, i, j, forced_col, sz](const vector<ChainStep> & chain, int dir, const ReasonLiterals & reason) {
                    // Materialise end >= pos_lb + lb(size) (for a variable size).
                    auto materialise_end = [&](const optional<ProofOnlySimpleIntegerVariableID> & end_opt, const optional<ProofLine> & end_ge,
                                               IntegerVariableID pos, IntegerVariableID size, Integer pos_lb) {
                        if (! end_opt)
                            return;
                        PolBuilder{}
                            .add(*end_ge)
                            .add_for_literal(logger->names_and_ids_tracker(), pos >= pos_lb)
                            .add_for_literal(logger->names_and_ids_tracker(), size >= state.lower_bound(size))
                            .emit(*logger, ProofLevel::Temporary);
                    };
                    auto pin = [&](BridgeMap & bridge, const optional<ProofOnlySimpleIntegerVariableID> & end_opt, const optional<ProofLine> & end_ge,
                                   IntegerVariableID pos, IntegerVariableID size, Integer coord, size_t r) -> ProofLine {
                        auto & bf = bridge.at(make_pair(r, coord));
                        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * bf.before >= 1_i, ProofLevel::Temporary);
                        materialise_end(end_opt, end_ge, pos, size, state.lower_bound(pos));
                        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * bf.after >= 1_i, ProofLevel::Temporary);
                        return logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * bf.active >= 1_i, ProofLevel::Temporary);
                    };
                    auto Lpol = [&](const BeforeFlagData & bf_ab, const BridgeFlags & aft_a, const BridgeFlags & bef_b,
                                    const optional<ProofLine> & aft_end_le) -> ProofLine {
                        PolBuilder pol;
                        pol.add(bf_ab.forward_line).add(aft_a.after_fwd).add(bef_b.before_fwd);
                        if (aft_end_le)
                            pol.add(*aft_end_le);
                        return pol.saturate().emit(*logger, ProofLevel::Temporary);
                    };

                    // Forced-axis elimination: both rects span forced_col, so
                    // neither forced-axis precedence holds; with the 4-way clause
                    // that leaves the free-axis disjunction.
                    auto Ax_i = pin(forced_bridge, forced_end[i], forced_end_ge[i], forced_pos[i], forced_size[i], forced_col, i);
                    auto Ax_j = pin(forced_bridge, forced_end[j], forced_end_ge[j], forced_pos[j], forced_size[j], forced_col, j);
                    auto & fx_i = forced_bridge.at(make_pair(i, forced_col));
                    auto & fx_j = forced_bridge.at(make_pair(j, forced_col));
                    auto Lf1 = Lpol(forced_before.at(make_pair(i, j)), fx_i, fx_j, forced_end_le[i]);
                    auto Lf2 = Lpol(forced_before.at(make_pair(j, i)), fx_j, fx_i, forced_end_le[j]);
                    PolBuilder rb;
                    rb.add(clause_lines.at(make_pair(min(i, j), max(i, j))))
                        .add(Lf1)
                        .add(Lf2)
                        .add(fx_i.active_fwd)
                        .add(fx_j.active_fwd)
                        .add(Ax_i)
                        .add(Ax_j);
                    add_escape_pins(rb, reason, i, j);
                    auto reduced = rb.saturate().emit(*logger, ProofLevel::Temporary);

                    // Free-axis chain: at each blocked cell t, both i (under the
                    // running bound / ext_lit) and j span t, contradicting the
                    // reduced clause, forcing the bound advance ext_lit.
                    for (size_t step = 0; step < chain.size(); ++step) {
                        auto t = chain[step].t;
                        auto ext_lit = dir > 0 ? (free_pos[i] > t) : (free_pos[i] < t - sz + 1_i);
                        auto A_blk = pin(free_bridge, free_end[j], free_end_ge[j], free_pos[j], free_size[j], t, j);
                        auto & fy_i = free_bridge.at(make_pair(i, t));
                        auto & fy_j = free_bridge.at(make_pair(j, t));
                        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * fy_i.before + 1_i * ext_lit >= 1_i, ProofLevel::Temporary);
                        // The pushed rect's after under ext_lit needs end >= s_lo
                        // + lb(size) (>= t+1), materialised under the extended
                        // reason (s_lo is the running bound / ¬ext_lit's bound).
                        materialise_end(free_end[i], free_end_ge[i], free_pos[i], free_size[i], chain[step].s_lo);
                        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * fy_i.after + 1_i * ext_lit >= 1_i, ProofLevel::Temporary);
                        auto A_psh = logger->emit_rup_proof_line_under_reason(
                            reason, WPBSum{} + 1_i * fy_i.active + 1_i * ext_lit >= 1_i, ProofLevel::Temporary);
                        auto Ly1 = Lpol(free_before.at(make_pair(i, j)), fy_i, fy_j, free_end_le[i]);
                        auto Ly2 = Lpol(free_before.at(make_pair(j, i)), fy_j, fy_i, free_end_le[j]);
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
                            logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * ext_lit >= 1_i, ProofLevel::Temporary);
                    }
                };

                // lb-push: i cannot fit below the blocker, push its origin up to
                // blk_hi -- capped at cur_hi + 1 (beyond that the domain is empty
                // and the chain would reference free cells i can never span).
                if (cur_lo > blk_lo - sz && cur_lo < blk_hi) {
                    auto target = min(blk_hi, cur_hi + 1_i);
                    vector<ChainStep> chain;
                    Integer running = cur_lo;
                    while (running < target) {
                        bool found = false;
                        for (Integer t = running + sz - 1_i; t >= running; --t)
                            if (is_blocked(t)) {
                                chain.push_back({t, running});
                                running = t + 1_i;
                                found = true;
                                break;
                            }
                        if (! found)
                            break;
                    }
                    auto justify = [&, chain](const ReasonLiterals & reason) -> void {
                        if (logger && logger->get_assertion_level() == AssertionLevel::Off)
                            emit_proof(chain, +1, reason);
                    };
                    inference.infer_greater_than_or_equal(
                        logger, free_pos[i], target, JustifyExplicitly{justify, ThenRUP::Yes, hints::Disjunctive2D{owner}}, generic_reason(rv));
                }
                // ub-push: i cannot fit above the blocker, push its origin down to
                // blk_lo - sz -- capped at cur_lo - 1 by the same reasoning.
                else if (cur_hi > blk_lo - sz && cur_hi < blk_hi) {
                    auto target = max(blk_lo - sz, cur_lo - 1_i);
                    vector<ChainStep> chain;
                    Integer running = cur_hi;
                    while (running > target) {
                        bool found = false;
                        for (Integer t = running; t <= running + sz - 1_i; ++t)
                            if (is_blocked(t)) {
                                chain.push_back({t, t - sz + 1_i});
                                running = t - sz;
                                found = true;
                                break;
                            }
                        if (! found)
                            break;
                    }
                    auto justify = [&, chain](const ReasonLiterals & reason) -> void {
                        if (logger && logger->get_assertion_level() == AssertionLevel::Off)
                            emit_proof(chain, -1, reason);
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
                        auto px = max(lst_xi, lst_xj);
                        push_axis(false, i, j, px); // free axis = y
                        push_axis(false, j, i, px);
                    }
                    if (y_overlap) {
                        auto py = max(lst_yi, lst_yj);
                        push_axis(true, i, j, py); // free axis = x
                        push_axis(true, j, i, py);
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
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom(_strict ? "disjunctive2d_strict" : "disjunctive2d"),
        SExpr::list(std::move(xs)), SExpr::list(std::move(ys)), SExpr::list(std::move(widths)), SExpr::list(std::move(heights))});
}
