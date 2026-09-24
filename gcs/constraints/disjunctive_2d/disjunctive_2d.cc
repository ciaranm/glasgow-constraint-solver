#include <gcs/constraints/disjunctive_2d/disjunctive_2d.hh>
#include <gcs/constraints/disjunctive_2d/hints.hh>
#include <gcs/constraints/innards/task_presence.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/comparator_network.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <algorithm>
#include <bit>
#include <map>
#include <memory>
#include <string>
#include <utility>
#include <variant>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::get;
using std::make_optional;
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
    /// The widest wire the cumulative relaxation's comparator network will
    /// build, as 1D's sorting certificate uses it: the guard coefficients are
    /// 2^width sized, so this is where an unbounded variable is turned away.
    constexpr int relaxation_max_width = 40;
}

Disjunctive2D::Disjunctive2D(vector<IntegerVariableID> xs, vector<IntegerVariableID> ys, vector<IntegerVariableID> widths,
    vector<IntegerVariableID> heights) : _xs(move(xs)), _ys(move(ys)), _widths(move(widths)), _heights(move(heights))
{
    if (_xs.size() != _ys.size() || _xs.size() != _widths.size() || _xs.size() != _heights.size())
        throw InvalidProblemDefinitionException{"Disjunctive2D: xs, ys, widths, heights must have the same size"};
    // Constant non-negativity is checked here; variable sizes are checked in
    // prepare(), where their domains first become available.
    for (const auto & w : _widths)
        if (is_constant_variable(w) && constant_value_of(w) < 0_i)
            throw InvalidProblemDefinitionException{"Disjunctive2D: widths must be non-negative"};
    for (const auto & h : _heights)
        if (is_constant_variable(h) && constant_value_of(h) < 0_i)
            throw InvalidProblemDefinitionException{"Disjunctive2D: heights must be non-negative"};
}

Disjunctive2D::Disjunctive2D(vector<IntegerVariableID> xs, vector<IntegerVariableID> ys, vector<Integer> widths, vector<Integer> heights) :
    Disjunctive2D(move(xs), move(ys), as_constant_variables(widths), as_constant_variables(heights))
{
}

Disjunctive2D::Disjunctive2D(vector<IntegerVariableID> xs, vector<IntegerVariableID> ys, vector<IntegerVariableID> widths,
    vector<IntegerVariableID> heights, vector<IntegerVariableID> presences) : Disjunctive2D(move(xs), move(ys), move(widths), move(heights))
{
    _presences = move(presences);
    if (_xs.size() != _presences.size())
        throw InvalidProblemDefinitionException{"Disjunctive2D: xs and presences must have the same size"};
    // A constant presence is checked here, by the rule that resolves it; a
    // variable one is checked in prepare(), where its domain first becomes
    // available.
    for (const auto & p : _presences)
        (void)task_presence(make_optional(p), "Disjunctive2D");
}

auto Disjunctive2D::presences() const -> const vector<IntegerVariableID> &
{
    return _presences;
}

auto Disjunctive2D::with_strict(std::optional<bool> strict) -> Disjunctive2D &
{
    _strict = strict.value_or(true);
    return *this;
}

auto Disjunctive2D::with_rules(Disjunctive2DRules rules) -> Disjunctive2D &
{
    _rules = rules;
    return *this;
}

auto Disjunctive2D::with_proof_mutation(Disjunctive2DProofMutation mutation) -> Disjunctive2D &
{
    _mutation = mutation;
    return *this;
}

auto Disjunctive2D::clone() const -> unique_ptr<Constraint>
{
    auto cloned = _presences.empty() ? make_unique<Disjunctive2D>(_xs, _ys, _widths, _heights)
                                     : make_unique<Disjunctive2D>(_xs, _ys, _widths, _heights, _presences);
    cloned->with_strict(_strict);
    cloned->with_rules(_rules);
    cloned->with_proof_mutation(_mutation);
    return cloned;
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

    // Resolve each rectangle's presence to the variable its separation clauses
    // have to carry a disjunct on, or nullopt when it is unconditionally
    // present, by the rule Cumulative and 1D Disjunctive resolve theirs with
    // --- these are alternative encodings of overlapping problems, so a
    // presence argument one honours and another drops would be a difference in
    // meaning between them with nothing recording it.
    _presence.assign(n, nullopt);
    vector<bool> never_present(n, false);
    for (size_t i = 0; i < n; ++i) {
        auto resolved = task_presence(_presences.empty() ? nullopt : make_optional(_presences[i]), "Disjunctive2D");
        _presence[i] = resolved.literal;
        never_present[i] = resolved.never_present;

        // Only now are the domains available, which is why a variable presence
        // is range-checked here rather than in the constructor.
        if (resolved.literal && ! is_constant_variable(*resolved.literal)) {
            auto [lo, hi] = initial_state.bounds(*resolved.literal);
            if (lo < 0_i || hi > 1_i)
                throw InvalidProblemDefinitionException{"Disjunctive2D: presences must be within {0, 1}"};
        }
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
        _width_vals.push_back(is_constant_variable(_widths[i]) ? constant_value_of(_widths[i]) : 0_i);
        width_ub.push_back(initial_state.upper_bound(_widths[i]));
        _height_vals.push_back(is_constant_variable(_heights[i]) ? constant_value_of(_heights[i]) : 0_i);
        height_ub.push_back(initial_state.upper_bound(_heights[i]));
    }

    // In non-strict mode, a rectangle whose width or height can only ever be 0
    // is zero-area and cannot overlap anything; drop it. In strict mode every
    // rectangle participates (its pairwise clauses remain in the OPB for leaf
    // correctness).
    // A constantly-absent rectangle is dropped in either mode: it occupies no
    // area, so it constrains nothing and nothing constrains it, and it must
    // appear nowhere in the encoding at all.
    _active_rects.reserve(n);
    for (size_t i = 0; i < n; ++i) {
        if (never_present[i])
            continue;
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

    // Which rectangles the cumulative relaxation can speak about, on each axis
    // in turn. Everything asked here is a property of the model rather than of
    // the search state, so the answer is the same whether or not proofs are
    // on, and the rule draws the same inferences either way --- which is what
    // keeps a proofs-off run from taking a different search path.
    //
    // A rectangle with a presence *variable* takes no part. Membership below is
    // decided from bounds alone, and a rectangle whose mandatory part covers a
    // time is taken to occupy it --- which an undecided presence does not, so
    // counting its height would prune the placements that need it absent. With
    // proofs on VeriPB rejects that (the separation clause carries a presence
    // disjunct no goal of the network's offers); with them off, a solve would
    // simply lose those solutions, so this is a decline rather than something
    // left to the checker.
    //
    // A *constant* presence never gets this far: task_presence resolves a
    // constant 1 to no literal at all, so such a rectangle is a plain one here
    // and takes part like any other, and a constant 0 has already been dropped
    // from _active_rects. So `_presence[i]` is set here only for a variable.
    //
    // That makes the decline coarser than it has to be: a presence variable
    // with the domain {1}, or one fixed to 1 during search, is present and is
    // still left out, for the whole solve, because membership is settled once
    // here. Taking such a rectangle part properly means putting its presence
    // literal in every fact list the certificate builds, so that the guard
    // covers the disjunct its clause brings in --- a larger change than this,
    // and nothing asks for it yet.
    //
    // A position variable two rectangles share is a bar to both of them. The
    // certificate states one fact per member per bound and guards every row by
    // the whole list at one uniform coefficient, and two members whose facts
    // are the same literal would put it there twice. Rectangles sharing a
    // handle are an edge case of `diffn` rather than a shape worth the
    // bookkeeping, so they take no part in this rule --- on either axis, since
    // a shared handle on one axis still appears in the other's reason.
    for (auto & members : _relaxation_members)
        members.clear();
    std::map<IntegerVariableID, size_t> position_uses;
    for (auto i : _active_rects) {
        ++position_uses[_xs[i]];
        ++position_uses[_ys[i]];
    }

    for (auto time_axis : {0, 1}) {
        const auto & time_pos = time_axis == 0 ? _xs : _ys;
        const auto & time_size = time_axis == 0 ? _widths : _heights;
        const auto & res_pos = time_axis == 0 ? _ys : _xs;
        const auto & res_size = time_axis == 0 ? _heights : _widths;
        for (auto i : _active_rects) {
            if (_presence[i])
                continue;
            if (position_uses[_xs[i]] > 1 || position_uses[_ys[i]] > 1)
                continue;
            // The sorted axis's size is the comparator network's duration,
            // which it pins to a constant and needs positive.
            if (! is_constant_variable(res_size[i]) || constant_value_of(res_size[i]) < 1_i)
                continue;
            // A wire reads a variable's own bit encoding, so the position has
            // to be a plain variable reading as an unsigned magnitude.
            if (! std::holds_alternative<SimpleIntegerVariableID>(res_pos[i]))
                continue;
            // The certificate weakens each pair's derived clause up to the
            // whole guard by naming the literals it is short of, so every
            // literal in the guard has to be one that can be named --- which
            // rules out a view, whose conditions reach the proof through their
            // defining rows instead.
            if (! std::holds_alternative<SimpleIntegerVariableID>(time_pos[i]))
                continue;
            if (! is_constant_variable(time_size[i]) && ! std::holds_alternative<SimpleIntegerVariableID>(time_size[i]))
                continue;
            if (initial_state.lower_bound(res_pos[i]) < 0_i)
                continue;
            // The network's guard coefficients are sized from its width, so a
            // variable declared over half the Integer range --- what an
            // unbounded FlatZinc int gets --- would overflow them long before
            // the proof got expensive enough to care.
            if (initial_state.upper_bound(res_pos[i]) + constant_value_of(res_size[i]) >= Integer{1ll << relaxation_max_width})
                continue;
            _relaxation_members[time_axis].push_back(i);
        }
    }

    return true;
}

auto Disjunctive2D::define_proof_model(ProofModel & model, const State &) -> void
{
    // Declarative pairwise OPB encoding (the diffn definition itself):
    //   for each axis d in {x, y} and ordered pair (i, j):
    //     before_{i,j,d} <-> pos_{i,d} + size_{i,d} <= pos_{j,d}
    //   then one separation clause per unordered pair:
    //     before_{i,j,x} + before_{j,i,x} + before_{i,j,y} + before_{j,i,y}
    //       [ + presences[i] = 0 + presences[j] = 0 ] >= 1
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
        // Ask what big-M the reifier is about to choose, rather than assuming:
        // the cumulative relaxation raises this row to the comparator
        // network's own guard coefficient, and the two directions of a pair
        // get different constants whenever their sizes or widths differ.
        auto guard = -model.names_and_ids_tracker().reification_shape(ineq, HalfReifyOnConjunctionOf{{flag}}).reif_coefficient;
        auto [fwd, rev] = model.add_two_way_reified_constraint(ineq, flag);
        return BeforeFlagData{flag, fwd, rev, guard};
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
            // And so does an absent one, which is the whole of what optional
            // rectangles add to this encoding: the presence literal is the
            // {0, 1} variable's single PB atom, so a pair of optional
            // rectangles costs two more terms in one clause they already had
            // --- no extra flag, no extra row, and nothing else in the encoding
            // has to know whether a rectangle is optional. In particular the
            // before flags stay reified *unconditionally* on the arithmetic,
            // which is what keeps every justification below a pol over the same
            // rows as before, and what makes the 4-way clause become 6-way
            // rather than something new.
            for (auto r : {i, j})
                if (_presence[r])
                    clause_sum += 1_i * (*_presence[r] == 0_i);
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
        // A rectangle starts blocking others the moment its presence is fixed
        // to 1, and stops being worth looking at when it is fixed to 0, so an
        // optional rectangle's presence has to wake the propagator as much as
        // its origin does.
        if (_presence[i] && ! is_constant_variable(*_presence[i]))
            triggers.on_instantiated.emplace_back(*_presence[i]);
    }

    propagators.install(
        constraint_id(),
        [xs = move(_xs), ys = move(_ys), width_var = move(_widths), height_var = move(_heights), active_rects = move(_active_rects),
            before_x = move(_before_x), before_y = move(_before_y), clause_lines = move(_clause_lines), zero_w = move(_zero_w),
            zero_h = move(_zero_h), presence = move(_presence), strict = _strict, rules = _rules, relaxation_members = move(_relaxation_members),
            mutation = _mutation, owner = constraint_id()](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
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

            // A rectangle with no presence variable is always here. An optional
            // one is here only once its presence is fixed to 1: until then it
            // occupies nothing that can be relied on, and it is absent once the
            // presence is fixed to 0.
            auto is_present = [&](size_t i) -> bool { return ! presence[i] || state.lower_bound(*presence[i]) == 1_i; };
            auto is_absent = [&](size_t i) -> bool { return presence[i] && state.upper_bound(*presence[i]) == 0_i; };

            // The presence literals a pairwise inference rests on: the pair's
            // own, and no others, because nothing here reasons about a third
            // rectangle. (1D Disjunctive and Cumulative build one list per
            // propagator call instead, since their profile and energy rules
            // speak about every task at once.) A rectangle with no presence
            // variable contributes nothing, so a non-optional constraint's
            // reasons are exactly what they were.
            auto reason_for = [&](size_t i, size_t j, const vector<IntegerVariableID> & vars) -> Reason {
                ReasonLiterals lits;
                for (auto r : {i, j})
                    if (presence[r] && is_present(r))
                        lits.push_back(*presence[r] == 1_i);
                return with_extra(generic_reason(vars), lits);
            };

            for (size_t a = 0; a < active_rects.size(); ++a) {
                auto i = active_rects[a];
                if (is_absent(i))
                    continue;
                auto [lst_xi, eet_xi] = mand(xs[i], wlb(i));
                auto [lst_yi, eet_yi] = mand(ys[i], hlb(i));
                if (lst_xi >= eet_xi || lst_yi >= eet_yi)
                    continue;
                for (size_t b = a + 1; b < active_rects.size(); ++b) {
                    auto j = active_rects[b];
                    if (is_absent(j))
                        continue;
                    auto [lst_xj, eet_xj] = mand(xs[j], wlb(j));
                    auto [lst_yj, eet_yj] = mand(ys[j], hlb(j));
                    if (lst_xj >= eet_xj || lst_yj >= eet_yj)
                        continue;
                    auto x_overlap = max(lst_xi, lst_xj) < min(eet_xi, eet_xj);
                    auto y_overlap = max(lst_yi, lst_yj) < min(eet_yi, eet_yj);
                    // Both undecided: the pair cannot both be there, but that
                    // is a two-literal fact with no single-variable conclusion
                    // to record, so leave it to whichever presence is decided
                    // first.
                    if (x_overlap && y_overlap && ! is_present(i) && ! is_present(j))
                        continue;
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

                        // Both present: no separating direction is available
                        // and the pair is infeasible.
                        if (is_present(i) && is_present(j)) {
                            inference.contradiction(
                                logger, JustifyExplicitly{justify, ThenRUP::Yes, hints::Disjunctive2D{owner}}, reason_for(i, j, rvars));
                            return PropagatorState::DisableUntilBacktrack;
                        }

                        // Exactly one is undecided, and it is the one that
                        // cannot be there: the same four pols refute all four
                        // separating directions, and the present one's
                        // presence literal is in the reason, so the six-way
                        // clause is left with the undecided one's own
                        // "absent" disjunct and the framework's closing RUP
                        // concludes it. Nothing here is conditional on a
                        // rectangle that might not be present --- the before
                        // flags are reified on the arithmetic alone.
                        auto undecided = is_present(i) ? j : i;
                        auto falsify = [&, undecided, justify](const ReasonLiterals & reason) -> void {
                            // The marker a test counts to show the rule fired,
                            // and counts to zero on the twin instance where it
                            // must not.
                            logger->emit_proof_comment("disjunctive2d optional: rectangle " + std::to_string(undecided) +
                                " would overlap one that is present, so it is absent");
                            justify(reason);
                        };
                        inference.infer_equal(logger, *presence[undecided], 0_i,
                            JustifyExplicitly{falsify, ThenRUP::Yes, hints::Disjunctive2D{owner}}, reason_for(i, j, rvars));
                        // i is gone, so there is nothing left to say about it
                        // against any later j.
                        if (undecided == i)
                            break;
                        continue;
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
                // A constant origin has no bound to push, and no order literal
                // for the certificate to cite. Where a push would have fired
                // its placement overlaps the blocker's mandatory part on both
                // axes, which is the pairwise contradiction's to refute.
                if (is_constant_variable(free_pos[i]))
                    return;
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

                // Every bound literal the justifications below cite, read now,
                // before the push. The justification runs after the push has
                // landed, and a position two rectangles share --- or one a push
                // has just wiped out --- would otherwise be read post-push: a
                // literal the reason does not support, or the bound of an
                // empty domain.
                auto forced_i_lb = lb_lit(forced_pos[i]), forced_i_ub = ub_lit(forced_pos[i]);
                auto forced_j_lb = lb_lit(forced_pos[j]), forced_j_ub = ub_lit(forced_pos[j]);
                auto free_j_lb = lb_lit(free_pos[j]), free_j_ub = ub_lit(free_pos[j]);

                // Both forced-axis precedences are refuted by the mandatory
                // overlap on that axis, exactly as in the contradiction.
                auto eliminate_forced_axis = [&, forced_i_lb, forced_i_ub, forced_j_lb, forced_j_ub]() -> void {
                    emit_before_pol(forced_before, forced_size, i, j, forced_i_lb, forced_j_ub);
                    emit_before_pol(forced_before, forced_size, j, i, forced_j_lb, forced_i_ub);
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
                    auto justify = [&, i, j, cur_lo = cur_lo, target, free_j_lb, free_j_ub, eliminate_forced_axis](
                                       const ReasonLiterals & reason) -> void {
                        pin_escapes(reason, i, j);
                        eliminate_forced_axis();
                        // Free axis: i entirely before j contradicts i's lower
                        // bound (it cannot fit below the blocker) ...
                        emit_before_pol(free_before, free_size, i, j, free_pos[i] >= cur_lo, free_j_ub);
                        // ... so j precedes i, putting pos_i at j's mandatory
                        // end or later, folded onto the target order literal's
                        // definition row: bf -> pos_i >= target.
                        emit_before_pol(free_before, free_size, j, i, free_j_lb, free_pos[i] < target);
                    };
                    inference.infer_greater_than_or_equal(
                        logger, free_pos[i], target, JustifyExplicitly{justify, ThenRUP::Yes, hints::Disjunctive2D{owner}}, reason_for(i, j, rv));
                }
                // ub-push: i cannot fit above the blocker, push its origin down to
                // blk_lo - sz -- capped at cur_lo - 1 by the same reasoning.
                else if (cur_hi > blk_lo - sz && cur_hi < blk_hi) {
                    auto target = max(blk_lo - sz, cur_lo - 1_i);
                    // As above: cur_hi is captured, not re-read, because the
                    // push has landed by justification time.
                    auto justify = [&, i, j, cur_hi = cur_hi, target, free_j_lb, free_j_ub, eliminate_forced_axis](
                                       const ReasonLiterals & reason) -> void {
                        pin_escapes(reason, i, j);
                        eliminate_forced_axis();
                        // Free axis: j entirely before i would put pos_i past
                        // its upper bound (i cannot fit above the blocker) ...
                        emit_before_pol(free_before, free_size, j, i, free_j_lb, free_pos[i] < cur_hi + 1_i);
                        // ... so i precedes j, capping pos_i at the blocker's
                        // latest start minus lb(size_i), folded onto the
                        // target: bf -> pos_i <= target.
                        emit_before_pol(free_before, free_size, i, j, free_pos[i] >= target + 1_i, free_j_ub);
                    };
                    inference.infer_less_than(logger, free_pos[i], target + 1_i,
                        JustifyExplicitly{justify, ThenRUP::Yes, hints::Disjunctive2D{owner}}, reason_for(i, j, rv));
                }
            };

            for (size_t a = 0; a < active_rects.size(); ++a) {
                auto i = active_rects[a];
                // A push is only sound between two rectangles that are both
                // there: an undecided one neither blocks (it might be absent)
                // nor may have its own bounds moved (the prune would be wrong
                // if it turns out absent, and there is no conditional-bounds
                // store to record it in). 1D leaves the same propagation on
                // the table for the same reason.
                if (! is_present(i))
                    continue;
                for (size_t b = a + 1; b < active_rects.size(); ++b) {
                    auto j = active_rects[b];
                    if (! is_present(j))
                        continue;
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

            // --- the cumulative relaxation (#972) ---------------------------
            //
            // Project onto one axis and the rectangles become a Cumulative:
            // task i has start pos_i and duration size_i on the time axis, and
            // height its size on the resource axis, on a resource whose
            // capacity is the extent the set is confined to there. That relaxation
            // sees conflicts the pairwise rule cannot --- three rectangles
            // sharing a time, no two of whose mandatory boxes overlap, can
            // still be too tall between them to fit.
            //
            // The proof side is what makes it interesting, because the
            // capacity row is not in the OPB and never will be (one encoding
            // per constraint). It is derived per firing instead: two
            // rectangles both occupying `t` can satisfy neither time-axis
            // disjunct of their 4-way separation clause, so what is left of
            // that clause separates them on the resource axis, and
            // ComparatorNetwork sorts the set's positions and telescopes to
            // "the window is at least as tall as the work in it" --- which the
            // firing says it is not. The set's members are the ones whose
            // *mandatory* parts cover `t`, so their occupancy is forced by
            // their bounds and no activity flag is minted anywhere.
            //
            // The separation clauses are therefore derived rather than model
            // rows, and so carry the reason; assume_with_guarded_separations is
            // what lets the network consume that.
            if (rules.cumulative_relaxation) {
                for (auto time_axis : {0, 1}) {
                    const auto & members = relaxation_members[time_axis];
                    if (members.size() < 2)
                        continue;

                    const auto & tpos = 0 == time_axis ? xs : ys;
                    const auto & tsize = 0 == time_axis ? width_var : height_var;
                    const auto & rpos = 0 == time_axis ? ys : xs;
                    const auto & rsize = 0 == time_axis ? height_var : width_var;
                    const auto & tbefore = 0 == time_axis ? before_x : before_y;
                    const auto & rbefore = 0 == time_axis ? before_y : before_x;
                    const auto & tzero = 0 == time_axis ? zero_w : zero_h;

                    // prepare() has already established, for every member, that
                    // the resource size is a positive constant and the resource
                    // position a plain variable a wire can read.
                    auto len = [&](size_t i) { return state.lower_bound(tsize[i]); };
                    auto tsize_is_var = [&](size_t i) { return ! is_constant_variable(tsize[i]); };
                    auto height = [&](size_t i) { return constant_value_of(rsize[i]); };
                    auto lst = [&](size_t i) { return state.upper_bound(tpos[i]); };
                    auto eet = [&](size_t i) { return state.lower_bound(tpos[i]) + len(i); };
                    auto covers = [&](size_t i, Integer t) { return lst(i) < eet(i) && t >= lst(i) && t < eet(i); };

                    // The set occupying `t`, and the window it needs: the
                    // smallest resource position any of them may take, and the
                    // largest position-plus-size. `extra` is the rectangle a
                    // push is asking about, which is added whether or not its
                    // own mandatory part reaches `t`.
                    struct Member
                    {
                        size_t rect;
                        /// This rectangle's resource-axis bounds and its
                        /// guaranteed time-axis length, snapshotted here rather
                        /// than re-read when the certificate runs: by then the
                        /// inference has landed, and a justification that read
                        /// the state again could cite a bound its own reason
                        /// does not carry.
                        Integer res_lo, res_hi, length;
                    };
                    struct Load
                    {
                        vector<Member> set;
                        Integer total{0}, lo{0}, hi{0};
                    };
                    auto load_at = [&](Integer t, optional<size_t> extra) -> Load {
                        Load result;
                        auto include = [&](size_t i) {
                            auto lo = state.lower_bound(rpos[i]), hi = state.upper_bound(rpos[i]);
                            result.lo = result.set.empty() ? lo : min(result.lo, lo);
                            result.hi = result.set.empty() ? hi + height(i) : max(result.hi, hi + height(i));
                            result.set.push_back(Member{i, lo, hi, len(i)});
                            result.total += height(i);
                        };
                        for (auto i : members)
                            if ((! extra || *extra != i) && covers(i, t))
                                include(i);
                        if (extra)
                            include(*extra);
                        return result;
                    };
                    auto overflows = [&](const Load & load) { return load.set.size() >= 2 && load.total > load.hi - load.lo; };

                    // The load profile only changes where a mandatory part
                    // starts or ends, so the set is constant between
                    // consecutive event points and testing each one tests every
                    // distinct set.
                    auto event_points = [&]() -> vector<Integer> {
                        vector<Integer> events;
                        for (auto i : members)
                            if (lst(i) < eet(i)) {
                                events.push_back(lst(i));
                                events.push_back(eet(i));
                            }
                        std::sort(events.begin(), events.end());
                        events.erase(std::unique(events.begin(), events.end()), events.end());
                        return events;
                    };

                    // The certificate. Every member of `set` occupies `t`,
                    // which for all but the pushed rectangle is a fact the
                    // reason states; for the pushed one, one of the two bounds
                    // is the negation of the conclusion instead, so the row the
                    // network lands on carries that literal and the framework's
                    // closing RUP reads the inference straight off it.
                    //
                    // Both time-axis bounds are stated *tightly* --- at
                    // `t - len + 1` and `t` rather than at the rectangle's own
                    // bounds --- which is not just a better nogood: it is what
                    // makes each pair's refutation cancel to degree exactly
                    // one, so that adding it to the 4-way clause leaves a
                    // clause rather than something of a higher degree.
                    auto emit_certificate = [&](Integer t, const Load & load, const ReasonLiterals & reason) -> void {
                        if (std::holds_alternative<disjunctive_2d_proof_mutation::EmitNothing>(mutation))
                            return;
                        auto & tracker = logger->names_and_ids_tracker();

                        // What each member contributes to the guard. `t_lo` and
                        // `t_hi` say it occupies `t`; `r_lo` and `r_hi` put it
                        // inside the window; `t_size` is what a variable
                        // time-axis size cancels against, and `escape` the
                        // non-strict zero-size disjunct its clause then carries.
                        // prepare() has already established that every one of
                        // these is over a plain variable, so each condition can
                        // be named as a literal as well as cancelled against.
                        using SimpleCondition = VariableConditionFrom<SimpleIntegerVariableID>;
                        struct MemberFacts
                        {
                            size_t rect;
                            SimpleIntegerVariableID r_var;
                            SimpleCondition t_lo, t_hi, r_lo, r_hi;
                            optional<SimpleCondition> t_size;
                            optional<ProofFlag> escape;
                        };
                        vector<MemberFacts> facts;
                        for (const auto & m : load.set) {
                            auto tv = get<SimpleIntegerVariableID>(tpos[m.rect]), rv = get<SimpleIntegerVariableID>(rpos[m.rect]);
                            facts.push_back(MemberFacts{m.rect, rv, tv >= t - m.length + 1_i, tv < t + 1_i, rv >= m.res_lo, rv < m.res_hi + 1_i,
                                tsize_is_var(m.rect) ? optional<SimpleCondition>{get<SimpleIntegerVariableID>(tsize[m.rect]) >= m.length} : nullopt,
                                tzero[m.rect]});
                        }

                        // Pin each zero-size escape false under the reason,
                        // exactly as the pairwise rule does, *as well as*
                        // carrying it in the guard below. The guard is what
                        // lets the network's arithmetic cancel the term the
                        // model's clause brings in; the pin is what lets the
                        // closing RUP discharge it. Without the pin that RUP
                        // has to get from `size >= 1` to `~escape` by bit
                        // arithmetic, which reaches one escape and no more ---
                        // the network's final row can force a single
                        // unassigned flag and not two --- so a firing with two
                        // of them was rejected.
                        if (! std::holds_alternative<disjunctive_2d_proof_mutation::SkipEscapePins>(mutation))
                            for (const auto & f : facts)
                                if (f.escape)
                                    logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * *f.escape <= 0_i, ProofLevel::Temporary);

                        auto width = static_cast<int>(std::bit_width(static_cast<unsigned long long>(load.hi.raw_value)));
                        for (const auto & f : facts) {
                            // A wire reads the variable's own bit encoding as
                            // an unsigned magnitude. prepare() keeps a negative
                            // domain out, which is what decides this; assert it
                            // here too, because a two's-complement sign bit
                            // sits at index zero and every guarded row built
                            // over it would be unsound rather than rejected.
                            if (tracker.num_bits(f.r_var) > 0_i && tracker.get_bit(f.r_var, 0_i).first != 1_i)
                                throw ProofError{"disjunctive2d cumulative relaxation wants an unsigned resource position"};
                            width = max(width, static_cast<int>(tracker.num_bits(f.r_var).raw_value));
                        }

                        ComparatorNetwork network(*logger, width, load.lo, load.hi, ProofLevel::Temporary);

                        // Every fact rides at the network's own coefficient, and
                        // uniformly: two rows guarded by the same reason at
                        // different coefficients cancel no better than two rows
                        // guarded by different reasons.
                        WPBSum guard;
                        auto guard_fact = [&](const SimpleCondition & cond) {
                            IntegerVariableCondition as_general = cond;
                            add_term_to(guard, network.big(), ! as_general);
                        };
                        for (const auto & f : facts) {
                            guard_fact(f.t_lo);
                            guard_fact(f.t_hi);
                            guard_fact(f.r_lo);
                            guard_fact(f.r_hi);
                            if (f.t_size)
                                guard_fact(*f.t_size);
                            // The fact is that the rectangle is not zero-sized,
                            // so it is the flag itself that goes in the guard.
                            if (f.escape)
                                guard += network.big() * *f.escape;
                        }
                        network.assume_with_guarded_separations(guard);

                        vector<ProofWire> wires;
                        for (const auto & f : facts) {
                            vector<ProofLiteralOrFlag> bits;
                            for (Integer b = 0_i; b < tracker.num_bits(f.r_var); ++b)
                                bits.push_back(ProofBitVariable{f.r_var, b, true});
                            wires.push_back(network.wire_over(bits));
                        }
                        for (size_t k = 0; k < facts.size(); ++k) {
                            network.add_task(wires[k], height(facts[k].rect));
                            network.set_bounds(wires[k]);
                        }

                        for (size_t a = 0; a < facts.size(); ++a)
                            for (size_t b = a + 1; b < facts.size(); ++b) {
                                auto i = facts[a].rect, j = facts[b].rect;

                                // One time-axis disjunct refuted: the before
                                // flag's [r] row says `pos_p + size_p <= pos_q`,
                                // and p occupying `t` at or after `t - size_p +
                                // 1` while q occupies it at or before `t` says
                                // otherwise. Exactly emit_before_pol's shape,
                                // against the certificate's own literals.
                                auto refute = [&](const MemberFacts & p, const MemberFacts & q) -> ProofLine {
                                    PolBuilder pol;
                                    pol.add(tbefore.at(make_pair(p.rect, q.rect)).forward_line);
                                    pol.add_for_literal(tracker, p.t_lo);
                                    if (p.t_size)
                                        pol.add_for_literal(tracker, *p.t_size);
                                    pol.add_for_literal(tracker, q.t_hi);
                                    return pol.saturate().emit(*logger, ProofLevel::Temporary);
                                };

                                // What is left of the 4-way clause once both
                                // time-axis disjuncts are gone: the pair is
                                // separated on the resource axis, under this
                                // pair's share of the guard. The network's goals
                                // offer the *whole* guard, so weaken up to it
                                // with literal axioms, which add a term without
                                // moving the degree.
                                PolBuilder clause;
                                clause.add(clause_lines.at(make_pair(min(i, j), max(i, j))));
                                clause.add(refute(facts[a], facts[b]));
                                if (! std::holds_alternative<disjunctive_2d_proof_mutation::SkipOneRefutation>(mutation))
                                    clause.add(refute(facts[b], facts[a]));
                                for (size_t k = 0;
                                    k < facts.size() && ! std::holds_alternative<disjunctive_2d_proof_mutation::SkipGuardWeakening>(mutation); ++k) {
                                    const auto & f = facts[k];
                                    if (k != a && k != b) {
                                        clause.add(! tracker.xliteral_for_ensuring(f.t_lo), 1_i, tracker);
                                        clause.add(! tracker.xliteral_for_ensuring(f.t_hi), 1_i, tracker);
                                        if (f.t_size)
                                            clause.add(! tracker.xliteral_for_ensuring(*f.t_size), 1_i, tracker);
                                        if (f.escape)
                                            clause.add(*f.escape, 1_i, tracker);
                                    }
                                    // No refutation mentions a resource-axis
                                    // bound, so every member's pair of them has
                                    // to be weakened in.
                                    clause.add(! tracker.xliteral_for_ensuring(f.r_lo), 1_i, tracker);
                                    clause.add(! tracker.xliteral_for_ensuring(f.r_hi), 1_i, tracker);
                                }
                                auto separated = clause.emit(*logger, ProofLevel::Temporary);

                                auto direction = [&](size_t p, size_t q) -> ModelSeparation {
                                    const auto & data = rbefore.at(make_pair(p, q));
                                    return ModelSeparation{data.flag, data.forward_line, data.forward_guard_coefficient};
                                };
                                network.add_separation(wires[a], direction(i, j), wires[b], direction(j, i), separated);
                            }

                        // The row this lands on says the window is at least as
                        // tall as the work in it, which the firing says it is
                        // not, so what survives is the clause over the guard's
                        // literals --- and the framework's closing RUP under the
                        // reason has only the conclusion left to read off it.
                        (void)network.sum_up(network.sort(wires));
                    };

                    // The reason: every fact the certificate assumes, except
                    // the one a push gets from negating its own conclusion.
                    auto reason_for = [&](Integer t, const Load & load, optional<size_t> pushed, bool synthetic_is_upper) -> Reason {
                        ReasonLiterals literals;
                        for (const auto & m : load.set) {
                            auto is_pushed = pushed && *pushed == m.rect;
                            if (! (is_pushed && ! synthetic_is_upper))
                                literals.push_back(ProofLiteral{tpos[m.rect] >= t - m.length + 1_i});
                            if (! (is_pushed && synthetic_is_upper))
                                literals.push_back(ProofLiteral{tpos[m.rect] < t + 1_i});
                            literals.push_back(ProofLiteral{rpos[m.rect] >= m.res_lo});
                            literals.push_back(ProofLiteral{rpos[m.rect] < m.res_hi + 1_i});
                            if (tsize_is_var(m.rect))
                                literals.push_back(ProofLiteral{tsize[m.rect] >= m.length});
                        }
                        return ExplicitReason{move(literals)};
                    };

                    // The overflow contradiction.
                    for (auto t : event_points()) {
                        auto load = load_at(t, nullopt);
                        if (! overflows(load))
                            continue;
                        auto justify = [&, t, load](const ReasonLiterals & reason) -> void {
                            if (! logger)
                                return;
                            logger->emit_proof_comment("disjunctive2d cumulative relaxation overflow axis=" + std::to_string(time_axis) +
                                " t=" + std::to_string(t.raw_value) + " w=" + std::to_string(load.set.size()));
                            emit_certificate(t, load, reason);
                        };
                        inference.contradiction(
                            logger, JustifyExplicitly{justify, ThenRUP::Yes, hints::Disjunctive2D{owner}}, reason_for(t, load, nullopt, false));
                        return PropagatorState::DisableUntilBacktrack;
                    }

                    // The bound pushes: a rectangle that cannot occupy a time
                    // without overflowing it is moved clear of that time. A
                    // rectangle whose own mandatory part already covers `t` is
                    // never selected, because the set it would be tested
                    // against is the one the contradiction pass has just found
                    // not to overflow --- which is also what stops a push from
                    // emptying a domain, since the conclusion's literal is then
                    // strictly inside it.
                    //
                    // A time gives the same verdict as every other time in the
                    // segment between two event points, so only the range's own
                    // ends and each segment's edge need testing.
                    auto blocked_in = [&](size_t j, Integer lo_t, Integer hi_t, bool want_largest) -> optional<Integer> {
                        if (lo_t > hi_t)
                            return nullopt;
                        // A time this rectangle's own mandatory part already
                        // covers is not a push: the set there is the one the
                        // overflow pass looks at, and if it overflows that is a
                        // contradiction rather than a bound to move. It can
                        // arise, because an earlier push this pass may have
                        // grown a mandatory part since that pass ran, and
                        // leaving it to the next round keeps the conclusion
                        // literal strictly inside the domain.
                        vector<Integer> candidates{want_largest ? hi_t : lo_t};
                        for (auto e : event_points())
                            if (e > lo_t && e <= hi_t)
                                candidates.push_back(want_largest ? e - 1_i : e);
                        std::sort(candidates.begin(), candidates.end());
                        candidates.erase(std::unique(candidates.begin(), candidates.end()), candidates.end());
                        if (want_largest)
                            std::reverse(candidates.begin(), candidates.end());
                        for (auto t : candidates)
                            if (! covers(j, t) && overflows(load_at(t, j)))
                                return t;
                        return nullopt;
                    };

                    auto push = [&](size_t j, Integer t, bool lower) {
                        auto load = load_at(t, j);
                        auto justify = [&, t, load, lower](const ReasonLiterals & reason) -> void {
                            if (! logger)
                                return;
                            logger->emit_proof_comment("disjunctive2d cumulative relaxation " + std::string{lower ? "lb" : "ub"} +
                                " axis=" + std::to_string(time_axis) + " t=" + std::to_string(t.raw_value) + " w=" + std::to_string(load.set.size()));
                            emit_certificate(t, load, reason);
                        };
                        auto justification = JustifyExplicitly{justify, ThenRUP::Yes, hints::Disjunctive2D{owner}};
                        if (lower)
                            inference.infer_greater_than_or_equal(logger, tpos[j], t + 1_i, justification, reason_for(t, load, j, true));
                        else
                            inference.infer_less_than(logger, tpos[j], t - len(j) + 1_i, justification, reason_for(t, load, j, false));
                    };

                    for (auto j : members) {
                        auto len_j = len(j);
                        if (len_j < 1_i)
                            continue;

                        // lb-push: with the origin at or after `cur_lo`, a
                        // blocked time within the rectangle's own length of it
                        // is one the rectangle would have to occupy, so the
                        // origin clears it.
                        auto [cur_lo, cur_hi] = state.bounds(tpos[j]);
                        if (cur_lo == cur_hi)
                            continue;
                        if (auto t = blocked_in(j, cur_lo, min(cur_hi, cur_lo + len_j - 1_i), true)) {
                            push(j, *t, true);
                            continue;
                        }

                        // ub-push: the mirror, with the origin at or before
                        // `cur_hi` and the smallest blocked time at or after it.
                        if (auto t = blocked_in(j, cur_hi, cur_hi + len_j - 1_i, false))
                            push(j, *t, false);
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
                if (! fixed(i) || ! zero_area(i) || ! is_present(i))
                    continue;
                auto xi = state.lower_bound(xs[i]), yi = state.lower_bound(ys[i]);
                for (auto j : active_rects) {
                    if (j == i || ! fixed(j) || ! is_present(j))
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
                        inference.contradiction(logger, JustifyUsingRUP{hints::Disjunctive2D{owner}}, reason_for(i, j, lr));
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
    // The optional forms are named apart from the plain ones rather than
    // sharing a name: cake_pb_cp dispatches on this, and it has no encoder for
    // an optional disjunctive2d, so a shared name would silently offer it the
    // non-optional encoding of a different constraint. Naming the gap is what
    // makes it a miss rather than a mismatch.
    if (_presences.empty())
        return _strict ? "disjunctive2d_strict" : "disjunctive2d";
    return _strict ? "disjunctive2d_strict_optional" : "disjunctive2d_optional";
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
    vector<SExpr> terms{SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(std::move(xs)),
        SExpr::list(std::move(ys)), SExpr::list(std::move(widths)), SExpr::list(std::move(heights))};
    // The presences list sits last, as it does for the 1D form, and is absent
    // altogether for a non-optional constraint --- whose s-expression must stay
    // exactly what it was.
    if (! _presences.empty()) {
        vector<SExpr> presences;
        for (const auto & p : _presences)
            presences.push_back(tracker.s_expr_term_of(p));
        terms.push_back(SExpr::list(std::move(presences)));
    }
    return SExpr::list(std::move(terms));
}
