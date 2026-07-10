#include <gcs/constraints/divide_modulus/divide_modulus.hh>
#include <gcs/constraints/divide_modulus/hints.hh>
#include <gcs/constraints/innards/arithmetic_utils.hh>
#include <gcs/constraints/innards/linear_stages.hh>
#include <gcs/constraints/innards/product_bounds.hh>
#include <gcs/constraints/innards/product_encoding.hh>
#include <gcs/constraints/innards/product_justify.hh>
#include <gcs/constraints/innards/tabulation.hh>
#include <gcs/constraints/innards/triggers.hh>
#include <gcs/constraints/linear/hints.hh>
#include <gcs/constraints/linear/propagate.hh>
#include <gcs/constraints/linear/utils.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/power.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>
#include <gcs/variable_condition.hh>

#include <algorithm>
#include <cstddef>
#include <limits>
#include <map>
#include <memory>
#include <optional>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_shared;
using std::make_unique;
using std::map;
using std::max;
using std::min;
using std::move;
using std::nullopt;
using std::numeric_limits;
using std::optional;
using std::pair;
using std::shared_ptr;
using std::string;
using std::to_string;
using std::tuple;
using std::unique_ptr;
using std::vector;

namespace
{
    // Is (x, y, q, r) in the truncated-division relation? That is, y is not
    // zero, x / y = q rounding towards zero, and r is the remainder (which
    // therefore takes the sign of x). Everything else in this file is
    // scaffolding to propagate exactly this.
    auto is_in_relation(Integer x, Integer y, Integer q, Integer r) -> bool
    {
        if (y == 0_i)
            return false;
        if (x.raw_value == numeric_limits<long long>::min() && y == -1_i)
            return false;
        return x.raw_value / y.raw_value == q.raw_value && x.raw_value % y.raw_value == r.raw_value;
    }

    // A non-negative magnitude STATE variable equal to |v|, channelled to v by cake's
    // <letter>ge0/<letter>lt0 channel (four half-reified rows @c[id][<letter>{ge0,lt0}_{ge,le}])
    // and carrying axis-<axis> free magnitude bits x[id][<axis>_*][bin]. mult_bc multiplies
    // these magnitudes, so its operands are always non-negative.
    struct CakeMagnitude
    {
        SimpleIntegerVariableID var;
        Integer num_bits;
        optional<ProofLine> pos_ge, pos_le, neg_ge, neg_le;
    };

    // The magnitude STATE variable and its bit count are allocated unconditionally so the
    // propagation runs with or without proofs; the channel rows and bit registration are only
    // emitted when there is a model (proofs on), leaving the channel lines nullopt otherwise.
    auto make_cake_magnitude(ProofModel * const model, State & state, const ConstraintID & owner, IntegerVariableID v, long long axis,
        const std::string & letter, const std::string & aux_name) -> CakeMagnitude
    {
        auto mag_ub = max(abs(state.lower_bound(v)), abs(state.upper_bound(v)));
        auto bits = 0_i;
        while (power2(bits) <= mag_ub)
            bits += 1_i;
        auto mag = state.allocate_integer_variable_with_state(0_i, power2(bits) - 1_i);
        if (! model)
            return {mag, bits, nullopt, nullopt, nullopt, nullopt};
        auto chan = product_enc::emit_magnitude_channel(*model, owner, v, mag, power2(bits) - 1_i, axis, letter, aux_name + to_string(mag.index));
        return {mag, bits, chan.pos_ge, chan.pos_le, chan.neg_ge, chan.neg_le};
    }

    // Everything the default (cake) divide/modulus propagation shares with its
    // justifications: the two non-negative magnitude operands, their bit-product
    // grid, and the remainder/identity row handles. The product w = |q| * |y|
    // exists nowhere -- not in the State and not in the proof: the propagator
    // computes its interval locally each call, and every justification talks
    // about the grid sum directly through the rem/id rows, which contain it
    // verbatim (cake's no-materialised-remainder design).
    // The local product interval, remembering which side established each
    // bound so the justifications can rebuild exactly that chain.
    enum class WSide
    {
        Mag,   // corner products of the magnitudes' bounds
        XPos,  // through the [x>=0]-gated rem/id rows
        XNeg,  // through the [x<1]-gated rem/id rows
        XDisj, // x's sign undecided: the two gated rows' disjunction, resolved by sign cases
    };

    struct WInterval
    {
        Integer lo, hi;
        WSide lo_side, hi_side;
    };

    namespace pj = gcs::innards::product_justify;

    struct DefaultProductData
    {
        SimpleIntegerVariableID mag_a{0}, mag_b{0}; // |q| (or the free quotient magnitude) and |y|
        IntegerVariableID x = 0_c;
        IntegerVariableID y = 0_c; // the signed divisor mag_b channels to
        // The divisor channel halves needed to push a magnitude lower bound
        // back through the hole: [y>=0] => y >= |y| and [y<0] => -y >= |y|.
        optional<ProofLine> ychan_pos_ge, ychan_neg_le;
        product_enc::BitProductGrid grid{}; // cells empty when proofs are off
        // Divide's remainder rows: 0 <= x - Sum < |y| gated [x>=0], and the
        // mirror 0 <= -x - Sum < |y| gated [x<1].
        optional<ProofLine> rem_pos_lo, rem_pos_hi, rem_neg_hi, rem_neg_lo;
        // Modulus's identity rows: r = x - Sum gated [x>=0], r = x + Sum gated [x<1].
        optional<ProofLine> id_pos_ge, id_pos_le, id_neg_ge, id_neg_le;

        // Constraint-lifetime caches of derived proof lines, keyed by the
        // bound values they were derived from. The bounds a search revisits
        // repeat heavily, so each distinct line is derived once, at
        // ProofLevel::Top (never deleted), under only the literals that
        // support it -- a subset of every citing inference's reason, so the
        // citing claim's negation discharges them. Proofs-only state: all
        // empty when proofs are off.
        map<tuple<IntegerVariableID, bool, Integer>, pj::ConditionalBound> operand_bound_lines;
        map<tuple<IntegerVariableID, bool, Integer>, pj::ConditionalBound> assumed_bound_lines;
        // magnitude-corner chain lines: (lower, a bound, b bound). Only the
        // Mag side lives here: its keys repeat heavily across the search and
        // each entry is a whole Subprocedure 7.1/7.2 grid derivation. The x
        // sides' keys churn with x's bounds, so a constraint-lifetime cache
        // of them would flood the checker's live database (every hint-free
        // RUP step pays for each standing constraint); they get a per-pass
        // cache instead.
        map<tuple<bool, Integer, Integer>, ProofLine> mag_chain_lines;
        // filter grid bounds: (lower, target, excluded bound, other bound)
        map<tuple<bool, IntegerVariableID, Integer, Integer>, pj::ConditionalBound> filter_grid_lines;
    };

    // The per-pass cache for the x-side chain lines, at ProofLevel::Current
    // (justification scopes forget Temporary lines; backtracking cleans
    // Current ones up, so the checker's live database stays bounded). Within
    // a pass the bounds are fixed, so (lower, side) identifies the line.
    struct PassChains
    {
        vector<pair<pair<bool, WSide>, ProofLine>> lines;
    };

    auto cached_operand_bound(ProofLogger & logger, DefaultProductData & d, IntegerVariableID v, bool lower, Integer bound) -> pj::ConditionalBound
    {
        auto key = tuple{v, lower, bound};
        if (auto it = d.operand_bound_lines.find(key); it != d.operand_bound_lines.end())
            return it->second;
        ReasonLiterals reason;
        reason.emplace_back(Literal{lower ? v >= bound : v <= bound});
        auto result = pj::derive_operand_bound(logger, reason, v, lower, bound, ProofLevel::Top);
        d.operand_bound_lines.emplace(key, result);
        return result;
    }

    auto cached_assumed_bound(ProofLogger & logger, DefaultProductData & d, IntegerVariableID v, bool lower, Integer bound) -> pj::ConditionalBound
    {
        auto key = tuple{v, lower, bound};
        if (auto it = d.assumed_bound_lines.find(key); it != d.assumed_bound_lines.end())
            return it->second;
        auto result = pj::derive_assumed_operand_bound(logger, v, lower, bound, ProofLevel::Top);
        d.assumed_bound_lines.emplace(key, result);
        return result;
    }

    // A line asserting Sum >= w.lo under the side's support literals, built
    // from whichever side currently gives that bound, cached for the
    // constraint's lifetime keyed by the bound values. For divide the x
    // sides go through the rem rows; for modulus through the identity rows
    // and r's bounds.
    auto grid_lower_line(ProofLogger & logger, const ReasonLiterals & reason, DefaultProductData & d, PassChains & pass, const WInterval & w,
        Integer a_lo, Integer b_lo, Integer x_lo, Integer x_hi, Integer b_hi,
        const optional<pair<IntegerVariableID, pair<Integer, Integer>>> & modulus_r) -> ProofLine
    {
        if (w.lo_side == WSide::Mag) {
            auto key = tuple{true, a_lo, b_lo};
            if (auto it = d.mag_chain_lines.find(key); it != d.mag_chain_lines.end())
                return it->second;
            auto a = cached_operand_bound(logger, d, d.mag_a, true, a_lo);
            auto b = cached_operand_bound(logger, d, d.mag_b, true, b_lo);
            auto line = pj::grid_sum_lower_bound(logger, reason, d.grid, d.mag_a, a, b, ProofLevel::Top).line;
            d.mag_chain_lines.emplace(key, line);
            return line;
        }
        auto key = pair{true, w.lo_side};
        for (const auto & [k, line] : pass.lines)
            if (k == key)
                return line;
        auto remember = [&](ProofLine line) {
            pass.lines.emplace_back(key, line);
            return line;
        };
        switch (w.lo_side) {
        case WSide::Mag: throw NonExhaustiveSwitch{}; // handled above
        case WSide::XPos: {
            PolBuilder builder;
            if (modulus_r) {
                // id_pos_le: Sum - x + r >= 0, so Sum >= x - r >= x_lo - r_hi
                builder.add(*d.id_pos_le);
                builder.add(cached_operand_bound(logger, d, d.x, true, x_lo).line);
                builder.add(cached_operand_bound(logger, d, modulus_r->first, false, modulus_r->second.second).line);
            }
            else {
                // rem_pos_hi: Sum - x + |y| >= 1, so Sum >= x - |y| + 1 >= x_lo - b_hi + 1
                builder.add(*d.rem_pos_hi);
                builder.add(cached_operand_bound(logger, d, d.x, true, x_lo).line);
                builder.add(cached_operand_bound(logger, d, d.mag_b, false, b_hi).line);
            }
            return remember(builder.emit(logger, ProofLevel::Current));
        }
        case WSide::XNeg: {
            PolBuilder builder;
            if (modulus_r) {
                // id_neg_le: Sum + x - r >= 0, so Sum >= r - x >= r_lo - x_hi
                builder.add(*d.id_neg_le);
                builder.add(cached_operand_bound(logger, d, d.x, false, x_hi).line);
                builder.add(cached_operand_bound(logger, d, modulus_r->first, true, modulus_r->second.first).line);
            }
            else {
                // rem_neg_lo: Sum + x + |y| >= 1, so Sum >= 1 - x - |y| >= 1 - x_hi - b_hi
                builder.add(*d.rem_neg_lo);
                builder.add(cached_operand_bound(logger, d, d.x, false, x_hi).line);
                builder.add(cached_operand_bound(logger, d, d.mag_b, false, b_hi).line);
            }
            return remember(builder.emit(logger, ProofLevel::Current));
        }
        case WSide::XDisj: {
            // x's sign undecided: derive the bound in each sign case (the same
            // chains as XPos/XNeg) and resolve them into one implication line.
            auto pos = WInterval{w.lo, w.hi, WSide::XPos, WSide::XPos};
            auto neg = WInterval{w.lo, w.hi, WSide::XNeg, WSide::XNeg};
            auto pos_line = grid_lower_line(logger, reason, d, pass, pos, a_lo, b_lo, x_lo, x_hi, b_hi, modulus_r);
            auto neg_line = grid_lower_line(logger, reason, d, pass, neg, a_lo, b_lo, x_lo, x_hi, b_hi, modulus_r);
            auto dims = vector<pj::SignCaseDimension>{{d.x >= 0_i, d.x < 0_i}};
            auto premises =
                vector<optional<pj::ConditionalBound>>{pj::ConditionalBound{d.grid.sum, w.lo, HalfReifyOnConjunctionOf{d.x >= 0_i}, pos_line},
                    pj::ConditionalBound{d.grid.sum, w.lo, HalfReifyOnConjunctionOf{d.x < 0_i}, neg_line}};
            auto concluded = pj::conclude_by_sign_cases(logger, reason, d.grid.sum >= w.lo, dims, premises);
            // restate at Current: the conclusion itself lands at Temporary
            PolBuilder copy;
            copy.add(concluded);
            return remember(copy.emit(logger, ProofLevel::Current));
        }
        }
        throw NonExhaustiveSwitch{};
    }

    // A line asserting -Sum >= -w.hi under the side's support literals,
    // likewise by side and cached.
    auto grid_upper_line(ProofLogger & logger, const ReasonLiterals & reason, DefaultProductData & d, PassChains & pass, const WInterval & w,
        Integer a_hi, Integer b_hi, Integer x_lo, Integer x_hi, const optional<pair<IntegerVariableID, pair<Integer, Integer>>> & modulus_r)
        -> ProofLine
    {
        if (w.hi_side == WSide::Mag) {
            auto key = tuple{false, a_hi, b_hi};
            if (auto it = d.mag_chain_lines.find(key); it != d.mag_chain_lines.end())
                return it->second;
            auto a = cached_operand_bound(logger, d, d.mag_a, false, a_hi);
            auto b = cached_operand_bound(logger, d, d.mag_b, false, b_hi);
            auto line = pj::grid_sum_upper_bound(logger, reason, d.grid, d.mag_a, d.mag_b, a, b, ProofLevel::Top).line;
            d.mag_chain_lines.emplace(key, line);
            return line;
        }
        auto key = pair{false, w.hi_side};
        for (const auto & [k, line] : pass.lines)
            if (k == key)
                return line;
        auto remember = [&](ProofLine line) {
            pass.lines.emplace_back(key, line);
            return line;
        };
        switch (w.hi_side) {
        case WSide::Mag: throw NonExhaustiveSwitch{}; // handled above
        case WSide::XPos: {
            PolBuilder builder;
            if (modulus_r) {
                // id_pos_ge: -Sum + x - r >= 0, so Sum <= x - r <= x_hi - r_lo
                builder.add(*d.id_pos_ge);
                builder.add(cached_operand_bound(logger, d, d.x, false, x_hi).line);
                builder.add(cached_operand_bound(logger, d, modulus_r->first, true, modulus_r->second.first).line);
            }
            else {
                // rem_pos_lo: -Sum + x >= 0, so Sum <= x <= x_hi
                builder.add(*d.rem_pos_lo);
                builder.add(cached_operand_bound(logger, d, d.x, false, x_hi).line);
            }
            return remember(builder.emit(logger, ProofLevel::Current));
        }
        case WSide::XNeg: {
            PolBuilder builder;
            if (modulus_r) {
                // id_neg_ge: -Sum - x + r >= 0, so Sum <= r - x <= r_hi - x_lo
                builder.add(*d.id_neg_ge);
                builder.add(cached_operand_bound(logger, d, d.x, true, x_lo).line);
                builder.add(cached_operand_bound(logger, d, modulus_r->first, false, modulus_r->second.second).line);
            }
            else {
                // rem_neg_hi: -Sum - x >= 0, so Sum <= -x <= -x_lo
                builder.add(*d.rem_neg_hi);
                builder.add(cached_operand_bound(logger, d, d.x, true, x_lo).line);
            }
            return remember(builder.emit(logger, ProofLevel::Current));
        }
        case WSide::XDisj: {
            auto pos = WInterval{w.lo, w.hi, WSide::XPos, WSide::XPos};
            auto neg = WInterval{w.lo, w.hi, WSide::XNeg, WSide::XNeg};
            auto pos_line = grid_upper_line(logger, reason, d, pass, pos, a_hi, b_hi, x_lo, x_hi, modulus_r);
            auto neg_line = grid_upper_line(logger, reason, d, pass, neg, a_hi, b_hi, x_lo, x_hi, modulus_r);
            auto dims = vector<pj::SignCaseDimension>{{d.x >= 0_i, d.x < 0_i}};
            auto premises =
                vector<optional<pj::ConditionalBound>>{pj::ConditionalBound{d.grid.neg_sum, -w.hi, HalfReifyOnConjunctionOf{d.x >= 0_i}, pos_line},
                    pj::ConditionalBound{d.grid.neg_sum, -w.hi, HalfReifyOnConjunctionOf{d.x < 0_i}, neg_line}};
            auto concluded = pj::conclude_by_sign_cases(logger, reason, d.grid.neg_sum >= -w.hi, dims, premises);
            // restate at Current: the conclusion itself lands at Temporary
            PolBuilder copy;
            copy.add(concluded);
            return remember(copy.emit(logger, ProofLevel::Current));
        }
        }
        throw NonExhaustiveSwitch{};
    }

    // One pass of the default-path product filtering: compute w = |q| * |y|'s
    // interval locally (mag-side corners intersected with what the rem/id rows
    // allow given x and, for modulus, r), then push back onto x (and r), onto
    // the magnitudes through the rows, and through the quotient filter. Every
    // inference is justified directly against the grid sum via the row that
    // carries it; the caller loops to fixpoint.
    template <typename Hint_>
    auto propagate_default_product(DefaultProductData & d, const optional<IntegerVariableID> & modulus_r, const State & state, auto & inference,
        ProofLogger * const logger, const ConstraintID & owner) -> void
    {
        auto [a_lo, a_hi] = state.bounds(d.mag_a);
        auto [b_lo, b_hi] = state.bounds(d.mag_b);
        auto [x_lo, x_hi] = state.bounds(d.x);
        auto r_bounds = modulus_r ? optional{state.bounds(*modulus_r)} : nullopt;
        auto r_for_lines = modulus_r ? optional{pair{*modulus_r, *r_bounds}} : nullopt;

        bool x_pos = x_lo >= 0_i, x_neg = x_hi < 1_i;

        // The local product interval, with provenance per side.
        auto [pw_lo, pw_hi] = product_bounds(a_lo, a_hi, b_lo, b_hi);
        WInterval w{max(pw_lo, 0_i), pw_hi, WSide::Mag, WSide::Mag};
        if (x_pos) {
            auto row_hi = modulus_r ? x_hi - r_bounds->first : x_hi;
            auto row_lo = modulus_r ? x_lo - r_bounds->second : x_lo - b_hi + 1_i;
            if (row_hi < w.hi) {
                w.hi = row_hi;
                w.hi_side = WSide::XPos;
            }
            if (row_lo > w.lo) {
                w.lo = row_lo;
                w.lo_side = WSide::XPos;
            }
        }
        else if (x_neg) {
            auto row_hi = modulus_r ? r_bounds->second - x_lo : -x_lo;
            auto row_lo = modulus_r ? r_bounds->first - x_hi : -x_hi - b_hi + 1_i;
            if (row_hi < w.hi) {
                w.hi = row_hi;
                w.hi_side = WSide::XNeg;
            }
            if (row_lo > w.lo) {
                w.lo = row_lo;
                w.lo_side = WSide::XNeg;
            }
        }
        else {
            // x's sign undecided: each gated row set bounds the grid in its own
            // branch, so the disjunction still bounds it, resolved by sign cases
            // in the justification.
            auto pos_hi = modulus_r ? x_hi - r_bounds->first : x_hi;
            auto neg_hi = modulus_r ? r_bounds->second - x_lo : -x_lo;
            auto pos_lo = modulus_r ? x_lo - r_bounds->second : x_lo - b_hi + 1_i;
            auto neg_lo = modulus_r ? r_bounds->first - x_hi : -x_hi - b_hi + 1_i;
            if (max(pos_hi, neg_hi) < w.hi) {
                w.hi = max(pos_hi, neg_hi);
                w.hi_side = WSide::XDisj;
            }
            if (min(pos_lo, neg_lo) > w.lo) {
                w.lo = min(pos_lo, neg_lo);
                w.lo_side = WSide::XDisj;
            }
        }

        // The reason literals that support each side of the interval.
        auto side_reason = [&](WSide side, bool for_lower) -> vector<Literal> {
            switch (side) {
            case WSide::Mag:
                if (for_lower)
                    return {d.mag_a >= a_lo, d.mag_b >= b_lo};
                else
                    return {d.mag_a <= a_hi, d.mag_b <= b_hi};
            case WSide::XPos:
                if (modulus_r)
                    return for_lower ? vector<Literal>{d.x >= x_lo, *modulus_r <= r_bounds->second, d.x >= 0_i}
                                     : vector<Literal>{d.x <= x_hi, *modulus_r >= r_bounds->first, d.x >= 0_i};
                else
                    return for_lower ? vector<Literal>{d.x >= x_lo, d.mag_b <= b_hi, d.x >= 0_i} : vector<Literal>{d.x <= x_hi, d.x >= 0_i};
            case WSide::XNeg:
                if (modulus_r)
                    return for_lower ? vector<Literal>{d.x <= x_hi, *modulus_r >= r_bounds->first, d.x < 1_i}
                                     : vector<Literal>{d.x >= x_lo, *modulus_r <= r_bounds->second, d.x < 1_i};
                else
                    return for_lower ? vector<Literal>{d.x <= x_hi, d.mag_b <= b_hi, d.x < 1_i} : vector<Literal>{d.x >= x_lo, d.x < 1_i};
            case WSide::XDisj:
                if (modulus_r)
                    return {d.x >= x_lo, d.x <= x_hi, *modulus_r >= r_bounds->first, *modulus_r <= r_bounds->second};
                else if (for_lower)
                    return {d.x >= x_lo, d.x <= x_hi, d.mag_b <= b_hi};
                else
                    return {d.x >= x_lo, d.x <= x_hi};
            }
            throw NonExhaustiveSwitch{};
        };

        auto as_reason = [&](vector<Literal> lits) {
            ReasonLiterals result;
            for (auto & l : lits)
                result.emplace_back(l);
            return ExplicitReason{move(result)};
        };

        auto merge_lits = [&](vector<Literal> a, const vector<Literal> & b) {
            a.insert(a.end(), b.begin(), b.end());
            return a;
        };

        // The per-pass x-side chain cache (see PassChains).
        PassChains pass;

        // The pass-level reasons the cached chains are derived under:
        // exactly the side's support literals, which every inference that
        // cites the chain merges into its own reason.
        auto chain_reason = [&](WSide side, bool for_lower) -> ReasonLiterals {
            ReasonLiterals result;
            for (auto & l : side_reason(side, for_lower))
                result.emplace_back(l);
            return result;
        };

        // An inconsistent interval refutes the node: both chains together.
        if (w.lo > w.hi) {
            auto justf = [&](const ReasonLiterals &) {
                // RUP cannot combine two opposing linear bounds on the grid
                // sum (a cutting-planes step), so add them explicitly.
                PolBuilder builder;
                builder.add(grid_lower_line(*logger, chain_reason(w.lo_side, true), d, pass, w, a_lo, b_lo, x_lo, x_hi, b_hi, r_for_lines));
                builder.add(grid_upper_line(*logger, chain_reason(w.hi_side, false), d, pass, w, a_hi, b_hi, x_lo, x_hi, r_for_lines));
                builder.emit(*logger, ProofLevel::Temporary);
            };
            inference.infer(logger, FalseLiteral{}, JustifyExplicitly{justf, ThenRUP::Yes, Hint_{owner}},
                as_reason(merge_lits(side_reason(w.lo_side, true), side_reason(w.hi_side, false))));
        }

        // Push the interval back onto x (and r for modulus) through the rows,
        // matching the gates: only once x's sign is decided.
        auto infer_bound = [&](const IntegerVariableID & var, bool lower, Integer value, auto make_lines, vector<Literal> reason_lits) -> void {
            if (lower ? value <= state.lower_bound(var) : value >= state.upper_bound(var))
                return;
            auto justf = [&, make_lines](const ReasonLiterals & reason) {
                PolBuilder builder;
                make_lines(builder, reason);
                builder.emit(*logger, ProofLevel::Temporary);
            };
            inference.infer(
                logger, lower ? var >= value : var < value + 1_i, JustifyExplicitly{justf, ThenRUP::Yes, Hint_{owner}}, as_reason(move(reason_lits)));
        };

        if (! modulus_r) {
            // Tight couplings that are only valid under a decided sign of x.
            if (x_pos)
                // x >= Sum >= mag corners (rem_pos_lo)
                infer_bound(
                    d.x, true, pw_lo,
                    [&](PolBuilder & builder, const ReasonLiterals &) {
                        builder.add(grid_lower_line(*logger, chain_reason(WSide::Mag, true), d, pass, WInterval{pw_lo, pw_hi, WSide::Mag, WSide::Mag},
                            a_lo, b_lo, x_lo, x_hi, b_hi, r_for_lines));
                        builder.add(*d.rem_pos_lo);
                    },
                    merge_lits(side_reason(WSide::Mag, true), {d.x >= 0_i}));
            else if (x_neg)
                // -x >= Sum (rem_neg_hi)
                infer_bound(
                    d.x, false, -pw_lo,
                    [&](PolBuilder & builder, const ReasonLiterals &) {
                        builder.add(grid_lower_line(*logger, chain_reason(WSide::Mag, true), d, pass, WInterval{pw_lo, pw_hi, WSide::Mag, WSide::Mag},
                            a_lo, b_lo, x_lo, x_hi, b_hi, r_for_lines));
                        builder.add(*d.rem_neg_hi);
                    },
                    merge_lits(side_reason(WSide::Mag, true), {d.x < 1_i}));
            else {
                // Sign undecided: a branch whose row cannot hold under the
                // magnitude product refutes that sign (the old gated stages'
                // contrapositive inference).
                if (pw_lo > x_hi)
                    infer_bound(
                        d.x, false, -1_i,
                        [&](PolBuilder & builder, const ReasonLiterals &) {
                            builder.add(grid_lower_line(*logger, chain_reason(WSide::Mag, true), d, pass,
                                WInterval{pw_lo, pw_hi, WSide::Mag, WSide::Mag}, a_lo, b_lo, x_lo, x_hi, b_hi, r_for_lines));
                            builder.add(*d.rem_pos_lo);
                        },
                        merge_lits(side_reason(WSide::Mag, true), {d.x <= x_hi}));
                if (pw_lo > -x_lo)
                    infer_bound(
                        d.x, true, 1_i,
                        [&](PolBuilder & builder, const ReasonLiterals &) {
                            builder.add(grid_lower_line(*logger, chain_reason(WSide::Mag, true), d, pass,
                                WInterval{pw_lo, pw_hi, WSide::Mag, WSide::Mag}, a_lo, b_lo, x_lo, x_hi, b_hi, r_for_lines));
                            builder.add(*d.rem_neg_hi);
                        },
                        merge_lits(side_reason(WSide::Mag, true), {d.x >= x_lo}));
            }

            // |x| <= Sum + |y| - 1 holds for either sign of x (the negation of
            // the claimed bound pins the sign, activating the matching row).
            infer_bound(
                d.x, false, pw_hi + b_hi - 1_i,
                [&](PolBuilder & builder, const ReasonLiterals &) {
                    builder.add(grid_upper_line(*logger, chain_reason(WSide::Mag, false), d, pass, WInterval{pw_lo, pw_hi, WSide::Mag, WSide::Mag},
                        a_hi, b_hi, x_lo, x_hi, r_for_lines));
                    builder.add(*d.rem_pos_hi);
                    builder.add(cached_operand_bound(*logger, d, d.mag_b, false, b_hi).line);
                },
                side_reason(WSide::Mag, false));
            infer_bound(
                d.x, true, -(pw_hi + b_hi - 1_i),
                [&](PolBuilder & builder, const ReasonLiterals &) {
                    builder.add(grid_upper_line(*logger, chain_reason(WSide::Mag, false), d, pass, WInterval{pw_lo, pw_hi, WSide::Mag, WSide::Mag},
                        a_hi, b_hi, x_lo, x_hi, r_for_lines));
                    builder.add(*d.rem_neg_lo);
                    builder.add(cached_operand_bound(*logger, d, d.mag_b, false, b_hi).line);
                },
                side_reason(WSide::Mag, false));

            // |y| >= |x| - Sum + 1 through whichever rem row's sign is decided.
            if (x_pos)
                infer_bound(
                    d.mag_b, true, x_lo - w.hi + 1_i,
                    [&](PolBuilder & builder, const ReasonLiterals &) {
                        builder.add(*d.rem_pos_hi);
                        builder.add(grid_upper_line(*logger, chain_reason(w.hi_side, false), d, pass, w, a_hi, b_hi, x_lo, x_hi, r_for_lines));
                        builder.add(cached_operand_bound(*logger, d, d.x, true, x_lo).line);
                    },
                    merge_lits(side_reason(w.hi_side, false), {d.x >= x_lo, d.x >= 0_i}));
            else if (x_neg)
                infer_bound(
                    d.mag_b, true, 1_i - x_hi - w.hi,
                    [&](PolBuilder & builder, const ReasonLiterals &) {
                        builder.add(*d.rem_neg_lo);
                        builder.add(grid_upper_line(*logger, chain_reason(w.hi_side, false), d, pass, w, a_hi, b_hi, x_lo, x_hi, r_for_lines));
                        builder.add(cached_operand_bound(*logger, d, d.x, false, x_hi).line);
                    },
                    merge_lits(side_reason(w.hi_side, false), {d.x <= x_hi, d.x < 1_i}));
        }
        else if (x_pos && modulus_r) {
            // r = x - Sum: both directions on r and on x
            infer_bound(
                *modulus_r, false, x_hi - w.lo,
                [&](PolBuilder & builder, const ReasonLiterals &) {
                    builder.add(*d.id_pos_ge);
                    builder.add(grid_lower_line(*logger, chain_reason(w.lo_side, true), d, pass, w, a_lo, b_lo, x_lo, x_hi, b_hi, r_for_lines));
                    builder.add(cached_operand_bound(*logger, d, d.x, false, x_hi).line);
                },
                merge_lits(side_reason(w.lo_side, true), {d.x <= x_hi, d.x >= 0_i}));
            infer_bound(
                *modulus_r, true, x_lo - w.hi,
                [&](PolBuilder & builder, const ReasonLiterals &) {
                    builder.add(*d.id_pos_le);
                    builder.add(grid_upper_line(*logger, chain_reason(w.hi_side, false), d, pass, w, a_hi, b_hi, x_lo, x_hi, r_for_lines));
                    builder.add(cached_operand_bound(*logger, d, d.x, true, x_lo).line);
                },
                merge_lits(side_reason(w.hi_side, false), {d.x >= x_lo, d.x >= 0_i}));
            infer_bound(
                d.x, true, r_bounds->first + w.lo,
                [&](PolBuilder & builder, const ReasonLiterals &) {
                    builder.add(*d.id_pos_ge);
                    builder.add(grid_lower_line(*logger, chain_reason(w.lo_side, true), d, pass, w, a_lo, b_lo, x_lo, x_hi, b_hi, r_for_lines));
                    builder.add(cached_operand_bound(*logger, d, *modulus_r, true, r_bounds->first).line);
                },
                merge_lits(side_reason(w.lo_side, true), {*modulus_r >= r_bounds->first, d.x >= 0_i}));
            infer_bound(
                d.x, false, r_bounds->second + w.hi,
                [&](PolBuilder & builder, const ReasonLiterals &) {
                    builder.add(*d.id_pos_le);
                    builder.add(grid_upper_line(*logger, chain_reason(w.hi_side, false), d, pass, w, a_hi, b_hi, x_lo, x_hi, r_for_lines));
                    builder.add(cached_operand_bound(*logger, d, *modulus_r, false, r_bounds->second).line);
                },
                merge_lits(side_reason(w.hi_side, false), {*modulus_r <= r_bounds->second, d.x >= 0_i}));
        }
        else if (x_neg && modulus_r) {
            // r = x + Sum
            infer_bound(
                *modulus_r, true, x_lo + w.lo,
                [&](PolBuilder & builder, const ReasonLiterals &) {
                    builder.add(*d.id_neg_ge);
                    builder.add(grid_lower_line(*logger, chain_reason(w.lo_side, true), d, pass, w, a_lo, b_lo, x_lo, x_hi, b_hi, r_for_lines));
                    builder.add(cached_operand_bound(*logger, d, d.x, true, x_lo).line);
                },
                merge_lits(side_reason(w.lo_side, true), {d.x >= x_lo, d.x < 1_i}));
            infer_bound(
                *modulus_r, false, x_hi + w.hi,
                [&](PolBuilder & builder, const ReasonLiterals &) {
                    builder.add(*d.id_neg_le);
                    builder.add(grid_upper_line(*logger, chain_reason(w.hi_side, false), d, pass, w, a_hi, b_hi, x_lo, x_hi, r_for_lines));
                    builder.add(cached_operand_bound(*logger, d, d.x, false, x_hi).line);
                },
                merge_lits(side_reason(w.hi_side, false), {d.x <= x_hi, d.x < 1_i}));
            infer_bound(
                d.x, true, r_bounds->first - w.hi,
                [&](PolBuilder & builder, const ReasonLiterals &) {
                    builder.add(*d.id_neg_le);
                    builder.add(grid_upper_line(*logger, chain_reason(w.hi_side, false), d, pass, w, a_hi, b_hi, x_lo, x_hi, r_for_lines));
                    builder.add(cached_operand_bound(*logger, d, *modulus_r, true, r_bounds->first).line);
                },
                merge_lits(side_reason(w.hi_side, false), {*modulus_r >= r_bounds->first, d.x < 1_i}));
            infer_bound(
                d.x, false, r_bounds->second - w.lo,
                [&](PolBuilder & builder, const ReasonLiterals &) {
                    builder.add(*d.id_neg_ge);
                    builder.add(grid_lower_line(*logger, chain_reason(w.lo_side, true), d, pass, w, a_lo, b_lo, x_lo, x_hi, b_hi, r_for_lines));
                    builder.add(cached_operand_bound(*logger, d, *modulus_r, false, r_bounds->second).line);
                },
                merge_lits(side_reason(w.lo_side, true), {*modulus_r <= r_bounds->second, d.x < 1_i}));
        }

        else if (modulus_r) {
            // x's sign undecided: an identity branch that cannot hold under the
            // magnitude product refutes that sign (the old gated stages'
            // contrapositive inference).
            if (pw_lo > x_hi - r_bounds->first)
                infer_bound(
                    d.x, false, -1_i,
                    [&](PolBuilder & builder, const ReasonLiterals &) {
                        builder.add(grid_lower_line(*logger, chain_reason(WSide::Mag, true), d, pass, WInterval{pw_lo, pw_hi, WSide::Mag, WSide::Mag},
                            a_lo, b_lo, x_lo, x_hi, b_hi, r_for_lines));
                        builder.add(*d.id_pos_ge);
                        builder.add(cached_operand_bound(*logger, d, *modulus_r, true, r_bounds->first).line);
                    },
                    merge_lits(side_reason(WSide::Mag, true), {d.x <= x_hi, *modulus_r >= r_bounds->first}));
            if (pw_hi < x_lo - r_bounds->second)
                infer_bound(
                    d.x, false, -1_i,
                    [&](PolBuilder & builder, const ReasonLiterals &) {
                        builder.add(grid_upper_line(*logger, chain_reason(WSide::Mag, false), d, pass,
                            WInterval{pw_lo, pw_hi, WSide::Mag, WSide::Mag}, a_hi, b_hi, x_lo, x_hi, r_for_lines));
                        builder.add(*d.id_pos_le);
                        builder.add(cached_operand_bound(*logger, d, *modulus_r, false, r_bounds->second).line);
                    },
                    merge_lits(side_reason(WSide::Mag, false), {d.x >= x_lo, *modulus_r <= r_bounds->second}));
            if (pw_lo > r_bounds->second - x_lo)
                infer_bound(
                    d.x, true, 1_i,
                    [&](PolBuilder & builder, const ReasonLiterals &) {
                        builder.add(grid_lower_line(*logger, chain_reason(WSide::Mag, true), d, pass, WInterval{pw_lo, pw_hi, WSide::Mag, WSide::Mag},
                            a_lo, b_lo, x_lo, x_hi, b_hi, r_for_lines));
                        builder.add(*d.id_neg_ge);
                        builder.add(cached_operand_bound(*logger, d, *modulus_r, false, r_bounds->second).line);
                    },
                    merge_lits(side_reason(WSide::Mag, true), {d.x >= x_lo, *modulus_r <= r_bounds->second}));
            if (pw_hi < r_bounds->first - x_hi)
                infer_bound(
                    d.x, true, 1_i,
                    [&](PolBuilder & builder, const ReasonLiterals &) {
                        builder.add(grid_upper_line(*logger, chain_reason(WSide::Mag, false), d, pass,
                            WInterval{pw_lo, pw_hi, WSide::Mag, WSide::Mag}, a_hi, b_hi, x_lo, x_hi, r_for_lines));
                        builder.add(*d.id_neg_le);
                        builder.add(cached_operand_bound(*logger, d, *modulus_r, true, r_bounds->first).line);
                    },
                    merge_lits(side_reason(WSide::Mag, false), {d.x <= x_hi, *modulus_r >= r_bounds->first}));
        }

        // The quotient filter, in both directions, justified by refuting the
        // excluded range against whichever chain established the violated
        // side of the interval (thesis Procedures 7.6/7.7, no sign cases:
        // both operands are magnitudes).
        auto filter_one = [&](SimpleIntegerVariableID target, Integer t_lo, Integer t_hi, SimpleIntegerVariableID other, Integer o_lo,
                              Integer o_hi) -> void {
            auto qf = quotient_filter(o_lo, o_hi, w.lo, w.hi);
            using Kind = QuotientFilter::Kind;
            switch (qf.kind) {
            case Kind::NoFilter: return;
            case Kind::EmptyBecauseYZero: {
                auto justf = [&](const ReasonLiterals &) {
                    grid_lower_line(*logger, chain_reason(w.lo_side, true), d, pass, w, a_lo, b_lo, x_lo, x_hi, b_hi, r_for_lines);
                    std::ignore = cached_operand_bound(*logger, d, other, false, 0_i);
                };
                inference.infer(logger, FalseLiteral{}, JustifyExplicitly{justf, ThenRUP::Yes, Hint_{owner}},
                    as_reason(merge_lits(side_reason(w.lo_side, true), {other <= 0_i})));
                return;
            }
            case Kind::Bounds: {
                if (qf.hi < t_hi) {
                    auto justf = [&, t = qf.hi](const ReasonLiterals & reason) {
                        auto w_hi_line = grid_upper_line(*logger, chain_reason(w.hi_side, false), d, pass, w, a_hi, b_hi, x_lo, x_hi, r_for_lines);
                        vector<Literal> zero_refs;
                        // Away from the zero endpoint the whole assumed-bound
                        // grid line depends only on (target, t, o_lo): cache it.
                        auto glb = [&]() -> pj::ConditionalBound {
                            if (o_lo >= 1_i) {
                                auto key = tuple{true, IntegerVariableID{target}, t, o_lo};
                                if (auto it = d.filter_grid_lines.find(key); it != d.filter_grid_lines.end())
                                    return it->second;
                                auto assumed = cached_assumed_bound(*logger, d, target, true, t + 1_i);
                                auto other_lb = cached_operand_bound(*logger, d, other, true, o_lo);
                                ReasonLiterals narrow;
                                narrow.emplace_back(Literal{other >= o_lo});
                                auto result = target == d.mag_a
                                    ? pj::grid_sum_lower_bound(*logger, narrow, d.grid, d.mag_a, assumed, other_lb, ProofLevel::Top)
                                    : pj::grid_sum_lower_bound(*logger, narrow, d.grid, d.mag_a, other_lb, assumed, ProofLevel::Top);
                                d.filter_grid_lines.emplace(key, result);
                                return result;
                            }
                            // the zero-endpoint drop: [other != 0] gives |other| >= 1,
                            // and the w-lower chain refutes [other = 0] by making the
                            // grid empty against a positive product
                            auto assumed = pj::derive_assumed_operand_bound(*logger, target, true, t + 1_i);
                            grid_lower_line(*logger, chain_reason(w.lo_side, true), d, pass, w, a_lo, b_lo, x_lo, x_hi, b_hi, r_for_lines);
                            auto cases = HalfReifyOnConjunctionOf{other != 0_i};
                            auto line = logger->emit_rup_proof_line(logger->reify(WPBSum{} + 1_i * other >= 1_i, cases), ProofLevel::Temporary);
                            zero_refs.emplace_back(other != 0_i);
                            auto other_lb = pj::ConditionalBound{WPBSum{} + 1_i * other, 1_i, cases, line};
                            return target == d.mag_a ? pj::grid_sum_lower_bound(*logger, reason, d.grid, d.mag_a, assumed, other_lb)
                                                     : pj::grid_sum_lower_bound(*logger, reason, d.grid, d.mag_a, other_lb, assumed);
                        }();
                        PolBuilder clash;
                        clash.add(glb.line).add(w_hi_line).saturate();
                        auto clause = clash.emit(*logger, ProofLevel::Temporary);
                        pj::conclude_by_sign_cases(
                            *logger, reason, WPBSum{} + -1_i * target >= -t, {}, {pj::ConditionalBound{WPBSum{}, 1_i, glb.cases, clause}}, zero_refs);
                    };
                    auto reason_lits = merge_lits(side_reason(w.hi_side, false), o_lo >= 1_i ? vector<Literal>{other >= o_lo} : vector<Literal>{});
                    if (o_lo < 1_i)
                        reason_lits = merge_lits(move(reason_lits), side_reason(w.lo_side, true));
                    inference.infer(logger, target < qf.hi + 1_i, JustifyExplicitly{justf, ThenRUP::Yes, Hint_{owner}}, as_reason(move(reason_lits)));
                }
                if (qf.lo > max(t_lo, 0_i)) {
                    auto justf = [&, t = qf.lo](const ReasonLiterals & reason) {
                        auto w_lo_line =
                            grid_lower_line(*logger, chain_reason(w.lo_side, true), d, pass, w, a_lo, b_lo, x_lo, x_hi, b_hi, r_for_lines);
                        // The assumed-bound grid line depends only on
                        // (target, t, o_hi): cache it.
                        auto gub = [&]() -> pj::ConditionalBound {
                            auto key = tuple{false, IntegerVariableID{target}, t, o_hi};
                            if (auto it = d.filter_grid_lines.find(key); it != d.filter_grid_lines.end())
                                return it->second;
                            auto assumed = cached_assumed_bound(*logger, d, target, false, t - 1_i);
                            auto other_ub = cached_operand_bound(*logger, d, other, false, o_hi);
                            ReasonLiterals narrow;
                            narrow.emplace_back(Literal{other <= o_hi});
                            auto result = target == d.mag_a
                                ? pj::grid_sum_upper_bound(*logger, narrow, d.grid, d.mag_a, d.mag_b, assumed, other_ub, ProofLevel::Top)
                                : pj::grid_sum_upper_bound(*logger, narrow, d.grid, d.mag_a, d.mag_b, other_ub, assumed, ProofLevel::Top);
                            d.filter_grid_lines.emplace(key, result);
                            return result;
                        }();
                        PolBuilder clash;
                        clash.add(gub.line).add(w_lo_line).saturate();
                        auto clause = clash.emit(*logger, ProofLevel::Temporary);
                        pj::conclude_by_sign_cases(
                            *logger, reason, WPBSum{} + 1_i * target >= t, {}, {pj::ConditionalBound{WPBSum{}, 1_i, gub.cases, clause}}, {});
                    };
                    inference.infer(logger, target >= qf.lo, JustifyExplicitly{justf, ThenRUP::Yes, Hint_{owner}},
                        as_reason(merge_lits(side_reason(w.lo_side, true), {other <= o_hi})));
                }
                return;
            }
            }
        };

        filter_one(d.mag_a, a_lo, a_hi, d.mag_b, b_lo, b_hi);
        filter_one(d.mag_b, b_lo, b_hi, d.mag_a, a_lo, a_hi);

        // Push the divisor magnitude's lower bound back through the hole:
        // |y| >= k excludes (-k, k), which only bites a bound when one side
        // is already gone. The channel stages cannot do this while y's sign
        // is undecided, but a sign-case resolution can.
        auto b_lo_now = state.lower_bound(d.mag_b);
        auto [y_lo_now, y_hi_now] = state.bounds(d.y);
        if (b_lo_now > y_hi_now && -b_lo_now < y_hi_now + 1_i) {
            auto justf = [&](const ReasonLiterals & reason) {
                auto mag_lb = cached_operand_bound(*logger, d, d.mag_b, true, b_lo_now);
                auto y_ub = cached_operand_bound(*logger, d, d.y, false, y_hi_now);
                PolBuilder pos_clash;
                pos_clash.add(*d.ychan_pos_ge).add(mag_lb.line).add(y_ub.line).saturate();
                auto pos_clause = pos_clash.emit(*logger, ProofLevel::Temporary);
                PolBuilder neg_bound;
                neg_bound.add(*d.ychan_neg_le).add(mag_lb.line);
                auto neg_line = neg_bound.emit(*logger, ProofLevel::Temporary);
                auto dims = vector<pj::SignCaseDimension>{{d.y >= 0_i, d.y < 0_i}};
                auto premises =
                    vector<optional<pj::ConditionalBound>>{pj::ConditionalBound{WPBSum{}, 1_i, HalfReifyOnConjunctionOf{d.y >= 0_i}, pos_clause},
                        pj::ConditionalBound{WPBSum{} + -1_i * d.y, b_lo_now, HalfReifyOnConjunctionOf{d.y < 0_i}, neg_line}};
                pj::conclude_by_sign_cases(*logger, reason, WPBSum{} + -1_i * d.y >= b_lo_now, dims, premises);
            };
            inference.infer(logger, d.y < -b_lo_now + 1_i, JustifyExplicitly{justf, ThenRUP::Yes, Hint_{owner}},
                as_reason({d.mag_b >= b_lo_now, d.y <= y_hi_now}));
        }
        else if (b_lo_now > -y_lo_now && b_lo_now > y_lo_now) {
            auto justf = [&](const ReasonLiterals & reason) {
                auto mag_lb = cached_operand_bound(*logger, d, d.mag_b, true, b_lo_now);
                auto y_lb = cached_operand_bound(*logger, d, d.y, true, y_lo_now);
                PolBuilder pos_bound;
                pos_bound.add(*d.ychan_pos_ge).add(mag_lb.line);
                auto pos_line = pos_bound.emit(*logger, ProofLevel::Temporary);
                PolBuilder neg_clash;
                neg_clash.add(*d.ychan_neg_le).add(mag_lb.line).add(y_lb.line).saturate();
                auto neg_clause = neg_clash.emit(*logger, ProofLevel::Temporary);
                auto dims = vector<pj::SignCaseDimension>{{d.y >= 0_i, d.y < 0_i}};
                auto premises = vector<optional<pj::ConditionalBound>>{
                    pj::ConditionalBound{WPBSum{} + 1_i * d.y, b_lo_now, HalfReifyOnConjunctionOf{d.y >= 0_i}, pos_line},
                    pj::ConditionalBound{WPBSum{}, 1_i, HalfReifyOnConjunctionOf{d.y < 0_i}, neg_clause}};
                pj::conclude_by_sign_cases(*logger, reason, WPBSum{} + 1_i * d.y >= b_lo_now, dims, premises);
            };
            inference.infer(
                logger, d.y >= b_lo_now, JustifyExplicitly{justf, ThenRUP::Yes, Hint_{owner}}, as_reason({d.mag_b >= b_lo_now, d.y >= y_lo_now}));
        }
    }

    // cake's sign atoms for one operand slot, in the two shapes the encoding
    // uses them: WPBSum terms for the sign/nonzero clauses, and gates for the
    // half-reified remainder/identity rows. A variable operand's atoms are its
    // reified conditions, exactly as before; a constant k's are its pinned
    // n[k][...] atoms, which is how cake encodes a constant slot (issue #483).
    struct OperandSignAtoms
    {
        PseudoBooleanTerm ge0, lt0, ge1, lt1, ne0;
        HalfReifyOnConjunctionOf ge0_gate, lt1_gate;
    };

    auto operand_sign_atoms(ProofModel & model, const IntegerVariableID & v) -> OperandSignAtoms
    {
        if (auto cv = get_if<ConstantIntegerVariableID>(&v)) {
            auto atoms = model.cake_constant_atoms(cv->const_value);
            return {atoms.ge0, ! atoms.ge0, atoms.ge1, ! atoms.ge1, ! atoms.eq0, HalfReifyOnConjunctionOf{atoms.ge0},
                HalfReifyOnConjunctionOf{! atoms.ge1}};
        }
        return {ProofLiteral{v >= 0_i}, ProofLiteral{v < 0_i}, ProofLiteral{v >= 1_i}, ProofLiteral{v < 1_i}, ProofLiteral{v != 0_i},
            HalfReifyOnConjunctionOf{v >= 0_i}, HalfReifyOnConjunctionOf{v < 1_i}};
    }

    // The four stages pinning mag = |v| in both directions off its cake channel, split on
    // sign(v). pos_threshold gates the non-negative half: 0 when v may be zero (the quotient),
    // 1 when v is known non-zero (the divisor). A constant operand's sign is static, so only
    // the matching half's stages exist, ungated: they pin mag = |v| at the root, and the
    // concluding RUP discharges the channel rows' pinned-atom gate terms.
    auto append_magnitude_stages(std::vector<LinearStage> & stages, SimpleIntegerVariableID mag, IntegerVariableID v, const CakeMagnitude & chan,
        Integer pos_threshold) -> void
    {
        optional<IntegerVariableCondition> pos_gate = v >= pos_threshold, neg_gate = v < 0_i;
        bool want_pos = true, want_neg = true;
        if (auto cv = get_if<ConstantIntegerVariableID>(&v)) {
            want_pos = cv->const_value >= pos_threshold;
            want_neg = cv->const_value < 0_i;
            pos_gate = nullopt;
            neg_gate = nullopt;
        }
        if (want_pos) {
            auto [t_le, m_le] = tidy_up_linear(WeightedSum{} + 1_i * mag + -1_i * v);
            stages.emplace_back(LinearStage{t_le, 0_i + m_le, false, {chan.pos_ge, nullopt}, pos_gate});
            auto [t_ge, m_ge] = tidy_up_linear(WeightedSum{} + -1_i * mag + 1_i * v);
            stages.emplace_back(LinearStage{t_ge, 0_i + m_ge, false, {chan.pos_le, nullopt}, pos_gate});
        }
        if (want_neg) {
            auto [t_nle, m_nle] = tidy_up_linear(WeightedSum{} + 1_i * mag + 1_i * v);
            stages.emplace_back(LinearStage{t_nle, 0_i + m_nle, false, {chan.neg_le, nullopt}, neg_gate});
            auto [t_nge, m_nge] = tidy_up_linear(WeightedSum{} + -1_i * mag + -1_i * v);
            stages.emplace_back(LinearStage{t_nge, 0_i + m_nge, false, {chan.neg_ge, nullopt}, neg_gate});
        }
    }

    // The shared decomposition: x = q * y + r, |r| < |y|, sign(r) = sign(x)
    // (or r = 0), all emitted as one flat @c[id][role] OPB block and run by
    // one propagator (issue #448). Divide exposes q and creates r as an
    // auxiliary; Modulus the other way around. Every operand shape -- views
    // and constants included -- goes through the one magnitude-product
    // machinery, matching cake_pb_cp's uniform encoding: a constant operand
    // just folds into the rows, gated on its pinned n[k][...] atoms (issue
    // #483). Once the user's variables are fixed, the multiplication must pin
    // the unbranched auxiliary (or fail) by propagation alone, and the
    // quotient filtering does exactly that.
    template <typename Hint_>
    auto install_divide_modulus(const ConstraintID & owner, bool expose_quotient, const IntegerVariableID & x, const IntegerVariableID & y,
        const IntegerVariableID & out, const std::variant<consistency::Auto, consistency::BC, consistency::Tabulated> & level,
        Propagators & propagators, State & initial_state, ProofModel * const optional_model) -> void
    {
        auto ax = affine_of(x), ay = affine_of(y), aout = affine_of(out);

        auto [xlo, xhi] = initial_state.bounds(x);

        // A structurally constant zero divisor makes the whole constraint
        // unsatisfiable, relationally rather than as an error.
        if ((! ay.var) && ay.offset == 0_i) {
            if (optional_model)
                optional_model->add_constraint(WPBSum{} >= 1_i);
            propagators.install_initial_contradiction("division by constant zero", JustifyUsingRUP{Hint_{owner}});
            return;
        }

        // The quotient magnitude can be no bigger than the dividend's (as
        // |y| >= 1 whenever the relation holds at all).
        auto mx = max(xlo < 0_i ? -xlo : xlo, xhi < 0_i ? -xhi : xhi);

        // Both routes emit cake_pb_cp's encoding: the product |q|*|y| lives only in the
        // bit-product grid feeding the remainder/identity rows, with no w (and, for
        // divide, no r) anywhere -- not in the OPB, not in the State, not in the proof.
        // Both directions multiply the two NON-NEGATIVE magnitudes, split the
        // identity/remainder on sign(x), and recover signed values in the tabulation -- a
        // single magnitude machinery covering every sign of both operands, views and
        // constants included: a constant operand's channel folds the constant into the
        // rows and gates on its pinned n[k][...] atoms, exactly as cake encodes a
        // constant slot (issue #483).
        //
        // Divide: the exposed slot is q. magq = |q| (a state var channelled to q by
        // cake's Zge0/Zlt0 channel) and absy = |y| (channelled by Yge0/Ylt0) are the
        // grid operands; cake's rem_* rows range 0 <= x - w < |y| over the grid sum and x
        // directly (rem_pos gated [x>=0], rem_neg gated [x<1]), so no remainder is
        // materialised at all. The exposed quotient's sign is pinned off the five sgn_*
        // clauses by RUP in the propagator. The tabulation enumerates only x, y, q; a
        // rejected leaf pins magq/absy by unit propagation from the assigned q, y and the
        // rem rows refute it.
        //
        // Modulus: the exposed slot is r, and cake leaves the quotient's
        // magnitude a FREE axis-0 bit-sum with no i[Q] channel (no Zge0/Zlt0, no sgn_*). The
        // aux is the quotient magnitude |q|; absy = |y| is the second grid operand. cake
        // splits the identity r = x -/+ |q||y| on sign(x), the range/sign rows bound r, and
        // the tabulation recovers the signed quotient sign(x)sign(y)|q|.

        // The exposed slot is the user's; the other is an auxiliary.
        IntegerVariableID q = 0_c, r = 0_c;
        SimpleIntegerVariableID aux = SimpleIntegerVariableID{0};
        if (expose_quotient) {
            q = out;
            // The divide path materialises no remainder (neither in the OPB nor in the
            // proof): cake's rem_* rows range x - w directly, so the aux is an inert state
            // slot, never introduced, enumerated, or meaningfully watched.
            aux = initial_state.allocate_integer_variable_with_state(0_i, 0_i);
            r = aux;
        }
        else {
            r = out;
            // The aux is the quotient MAGNITUDE |q|, a free axis-0 bit-sum sized by the
            // dividend's magnitude (|q| <= |x| since |y| >= 1). Its provable range is the
            // bit-implied [0, 2^n - 1]; give the state that range (like divide's product w)
            // and register its bits in cake's x[id][0_*][bin] naming with no OPB bounds, so
            // they ARE the magnitude the bit products multiply. The signed quotient is never
            // materialised: the propagation is in magnitude space and the tabulation recovers
            // sign(x)sign(y)|q| for its relation check.
            auto q_bits = 0_i;
            while (power2(q_bits) <= mx)
                q_bits += 1_i;
            auto q_bit_max = power2(q_bits) - 1_i;
            aux = initial_state.allocate_integer_variable_with_state(0_i, q_bit_max);
            if (optional_model)
                optional_model->register_state_variable_bits_in_proof(
                    aux, 0_i, q_bit_max, "aux_modulus_quotient" + to_string(aux.index), CakeBitNaming{owner, {0}, "bin", nullopt, false, true});
            q = aux;
        }

        shared_ptr<DefaultProductData> default_data;
        shared_ptr<vector<LinearStage>> default_stages;

        if (expose_quotient) {
            // Divide, any sign of the dividend. BOTH the x >= 0 and x < 0 remainder rows
            // are live, each gated on sign(x) so only the matching regime fires once x is
            // branched. The quotient's sign is pinned off the sgn_* clauses (for whichever
            // signs of x and y are established). No remainder is materialised, and neither
            // is the product w = |q||y|: cake's rem_* rows range x against the bit-product
            // grid sum directly, the propagator computes w's interval locally each call,
            // and the justifications cite the rows and the grid (no in-proof
            // reformulation). The tabulation enumerates only x, y, q.
            auto q_eff = q, y_eff = y, x_eff = x;

            // magq = |q| (Z channel to the exposed quotient) and absy = |y| (channelled by
            // Yge0/Ylt0) are the two non-negative grid operands. The magnitude state vars
            // are allocated regardless of proofs.
            auto zchan = make_cake_magnitude(optional_model, initial_state, owner, q_eff, 0, "Z", "aux_divide_qmag");
            auto ychan = make_cake_magnitude(optional_model, initial_state, owner, y_eff, 1, "Y", "aux_divide_absdivisor");
            auto magq = zchan.var, absy = ychan.var;

            default_data = make_shared<DefaultProductData>();
            default_data->mag_a = magq;
            default_data->mag_b = absy;
            default_data->x = x_eff;
            default_data->y = y_eff;
            default_data->ychan_pos_ge = ychan.pos_ge;
            default_data->ychan_neg_le = ychan.neg_le;

            // Stages: just the magq (0-3) and absy (4-7) channels; the x/product coupling
            // lives in propagate_default_product.
            default_stages = make_shared<vector<LinearStage>>();
            append_magnitude_stages(*default_stages, magq, q_eff, zchan, 0_i);
            append_magnitude_stages(*default_stages, absy, y_eff, ychan, 1_i);

            if (optional_model) {
                default_data->grid = product_enc::emit_bit_product_grid(*optional_model, owner, magq, absy, product_enc::LinkNaming{});
                const auto & product_sum = default_data->grid.sum;
                const auto & neg_product = default_data->grid.neg_sum;

                auto xa = operand_sign_atoms(*optional_model, x);
                auto ya = operand_sign_atoms(*optional_model, y);
                auto qa = operand_sign_atoms(*optional_model, q);

                // Both remainder-row sets: 0 <= x - |q||y| < |y| (rem_pos, gated [x>=0]) and
                // 0 <= -x - |q||y| < |y| (rem_neg, gated [x<1]).
                default_data->rem_pos_lo =
                    optional_model->add_labelled_constraint(owner, "rem_pos_lo", neg_product + 1_i * x_eff >= 0_i, xa.ge0_gate);
                default_data->rem_pos_hi =
                    optional_model->add_labelled_constraint(owner, "rem_pos_hi", product_sum + -1_i * x_eff + 1_i * absy >= 1_i, xa.ge0_gate);
                default_data->rem_neg_hi =
                    optional_model->add_labelled_constraint(owner, "rem_neg_hi", neg_product + -1_i * x_eff >= 0_i, xa.lt1_gate);
                default_data->rem_neg_lo =
                    optional_model->add_labelled_constraint(owner, "rem_neg_lo", product_sum + 1_i * x_eff + 1_i * absy >= 1_i, xa.lt1_gate);

                optional_model->add_labelled_constraint(owner, "sgn_pp", WPBSum{} + 1_i * xa.lt1 + 1_i * ya.lt1 + 1_i * qa.ge0 >= 1_i);
                optional_model->add_labelled_constraint(owner, "sgn_nn", WPBSum{} + 1_i * xa.ge0 + 1_i * ya.ge0 + 1_i * qa.ge0 >= 1_i);
                optional_model->add_labelled_constraint(owner, "sgn_pn", WPBSum{} + 1_i * xa.lt1 + 1_i * ya.ge0 + 1_i * qa.lt1 >= 1_i);
                optional_model->add_labelled_constraint(owner, "sgn_np", WPBSum{} + 1_i * xa.ge0 + 1_i * ya.lt1 + 1_i * qa.lt1 >= 1_i);
                optional_model->add_labelled_constraint(owner, "sgn_x0", WPBSum{} + 1_i * xa.ne0 + 1_i * qa.lt1 >= 1_i);
                optional_model->add_labelled_constraint(owner, "nonzero", WPBSum{} + 1_i * ya.ge1 + 1_i * ya.lt0 >= 1_i);
            }
        }
        else {
            // The default modulus path: the exposed slot is r; the quotient magnitude |q| (the
            // aux, axis-0 free magnitude) and the divisor magnitude |y| (absy, pinned to |y| by
            // cake's Yge0/Ylt0 channel) multiply through the bit-product grid. The identity
            // splits on sign(x): r = x - Sum off id_pos_* (gated [x>=0]) and r = x + Sum off
            // id_neg_* (gated [x<0]); the range/sign rows bound 0 <= r < |y| (x>=0) or
            // -|y| < r <= 0 (x<0). Both grid operands are non-negative, so the quotient
            // filtering needs no signed reasoning. The product w = |q||y| exists nowhere:
            // the propagator computes its interval locally from the magnitudes and from
            // x and r through the identity rows, and the justifications cite those rows
            // and the grid directly.
            //
            // r and the operands are the plain underlying *aout.var / *a*.var, not view
            // wrappers: the identity inferences propagate the exposed r off the wide grid
            // interval, and deviewing that defeats the reverse unit propagation.
            auto y_eff = y, x_eff = x, r_eff = out;
            auto q_eff = aux; // the free quotient magnitude

            auto ychan = make_cake_magnitude(optional_model, initial_state, owner, y_eff, 1, "Y", "aux_modulus_absdivisor");
            auto absy = ychan.var;

            default_data = make_shared<DefaultProductData>();
            default_data->mag_a = q_eff;
            default_data->mag_b = absy;
            default_data->x = x_eff;
            default_data->y = y_eff;
            default_data->ychan_pos_ge = ychan.pos_ge;
            default_data->ychan_neg_le = ychan.neg_le;

            // The range/sign OPB lines feed their stages below; they exist only proofs-on, so
            // the stages carry nullopt lines (and filter on their terms) proofs-off.
            optional<ProofLine> rng_hi, rng_lo, sgn_pos, sgn_neg;
            default_stages = make_shared<vector<LinearStage>>();

            if (optional_model) {
                default_data->grid = product_enc::emit_bit_product_grid(*optional_model, owner, q_eff, absy, product_enc::LinkNaming{});
                const auto & product_sum = default_data->grid.sum;
                const auto & neg_product = default_data->grid.neg_sum;

                auto xa = operand_sign_atoms(*optional_model, x);
                auto ya = operand_sign_atoms(*optional_model, y);

                optional_model->add_labelled_constraint(owner, "nonzero", WPBSum{} + 1_i * ya.ge1 + 1_i * ya.lt0 >= 1_i);

                // r = x - |q||y|, split on sign(x): id_pos_* (gated [x>=0], r = x - Sum) and
                // id_neg_* (gated [x<0], r = x + Sum -- since for x < 0 the quotient product
                // q*y has sign(x), i.e. q*y = -Sum).
                default_data->id_pos_ge =
                    optional_model->add_labelled_constraint(owner, "id_pos_ge", neg_product + 1_i * x_eff + -1_i * r_eff >= 0_i, xa.ge0_gate);
                default_data->id_pos_le =
                    optional_model->add_labelled_constraint(owner, "id_pos_le", product_sum + -1_i * x_eff + 1_i * r_eff >= 0_i, xa.ge0_gate);
                default_data->id_neg_ge =
                    optional_model->add_labelled_constraint(owner, "id_neg_ge", neg_product + -1_i * x_eff + 1_i * r_eff >= 0_i, xa.lt1_gate);
                default_data->id_neg_le =
                    optional_model->add_labelled_constraint(owner, "id_neg_le", product_sum + 1_i * x_eff + -1_i * r_eff >= 0_i, xa.lt1_gate);

                // |r| < |y| = absy: rng_hi (r < absy) and rng_lo (r > -absy), plus the r-sign
                // rows (r takes x's sign; sgn_pos gated [x>=0], sgn_neg gated [x<0]).
                rng_hi = optional_model->add_labelled_constraint(owner, "rng_hi", WPBSum{} + -1_i * r_eff + 1_i * absy >= 1_i);
                rng_lo = optional_model->add_labelled_constraint(owner, "rng_lo", WPBSum{} + 1_i * r_eff + 1_i * absy >= 1_i);
                sgn_pos = optional_model->add_labelled_constraint(owner, "sgn_pos", WPBSum{} + 1_i * r_eff >= 0_i, xa.ge0_gate);
                sgn_neg = optional_model->add_labelled_constraint(owner, "sgn_neg", WPBSum{} + -1_i * r_eff >= 0_i, xa.lt1_gate);
            }

            // Stages (built regardless of proofs): the range 0 <= r < absy (x>=0) /
            // -absy < r <= 0 (x<0) via rng_hi/rng_lo (ungated, valid for either sign), the
            // r-sign stages sgn_pos/sgn_neg, and absy = |y| off the Yge0/Ylt0 channel. The
            // identity coupling of r, x and the grid lives in propagate_default_product.
            auto [t_rhi, m_rhi] = tidy_up_linear(WeightedSum{} + 1_i * r_eff + -1_i * absy);
            default_stages->emplace_back(LinearStage{t_rhi, -1_i + m_rhi, false, {rng_hi, nullopt}, nullopt});
            auto [t_rlo, m_rlo] = tidy_up_linear(WeightedSum{} + -1_i * r_eff + -1_i * absy);
            default_stages->emplace_back(LinearStage{t_rlo, -1_i + m_rlo, false, {rng_lo, nullopt}, nullopt});
            auto [t_slo, m_slo] = tidy_up_linear(WeightedSum{} + -1_i * r_eff);
            default_stages->emplace_back(LinearStage{t_slo, 0_i + m_slo, false, {sgn_pos, nullopt}, optional{x_eff >= 0_i}});
            auto [t_shi, m_shi] = tidy_up_linear(WeightedSum{} + 1_i * r_eff);
            default_stages->emplace_back(LinearStage{t_shi, 0_i + m_shi, false, {sgn_neg, nullopt}, optional{x_eff < 1_i}});
            // absy = |y| off the Y channel, split on sign(y).
            append_magnitude_stages(*default_stages, absy, y_eff, ychan, 1_i);
        }

        Triggers triggers;
        vector<IntegerVariableID> watched;
        auto watch = [&](const IntegerVariableID & v) {
            if (! holds_alternative<ConstantIntegerVariableID>(v) && std::find(watched.begin(), watched.end(), v) == watched.end())
                watched.push_back(v);
        };
        watch(x);
        watch(y);
        watch(out);
        watch(aux);
        watch(default_data->mag_a);
        watch(default_data->mag_b);
        triggers.on_bounds = watched;

        propagators.install(
            owner,
            [data = default_data, stg = default_stages, y = y, q = q, x = x, pin_q_sign = expose_quotient,
                modulus_r = expose_quotient ? optional<IntegerVariableID>{} : optional{out},
                owner = owner](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                do {
                    if (state.in_domain(y, 0_i))
                        inference.infer(logger, y != 0_i, JustifyUsingRUP{Hint_{owner}}, ExplicitReason{ReasonLiterals{}});

                    if (pin_q_sign) {
                        // The grid carries no signed reasoning, so the exposed quotient's
                        // sign is pinned off the sgn_* clauses by RUP once the signs of x
                        // and y are both established. sgn_pp: x>0 & y>0 -> q>=0; sgn_pn:
                        // x>0 & y<0 -> q<=0; sgn_nn: x<0 & y<0 -> q>=0; sgn_np: x<0 & y>0
                        // -> q<=0.
                        if (state.lower_bound(x) >= 1_i) {
                            if (state.lower_bound(y) >= 1_i && state.lower_bound(q) < 0_i)
                                inference.infer(logger, q >= 0_i, JustifyUsingRUP{Hint_{owner}}, ExplicitReason{ReasonLiterals{x >= 1_i, y >= 1_i}});
                            else if (state.upper_bound(y) < 0_i && state.upper_bound(q) > 0_i)
                                inference.infer(logger, q < 1_i, JustifyUsingRUP{Hint_{owner}}, ExplicitReason{ReasonLiterals{x >= 1_i, y < 0_i}});
                        }
                        else if (state.upper_bound(x) < 0_i) {
                            if (state.upper_bound(y) < 0_i && state.lower_bound(q) < 0_i)
                                inference.infer(logger, q >= 0_i, JustifyUsingRUP{Hint_{owner}}, ExplicitReason{ReasonLiterals{x < 0_i, y < 0_i}});
                            else if (state.lower_bound(y) >= 1_i && state.upper_bound(q) > 0_i)
                                inference.infer(logger, q < 1_i, JustifyUsingRUP{Hint_{owner}}, ExplicitReason{ReasonLiterals{x < 0_i, y >= 1_i}});
                        }
                    }

                    if (! propagate_stages(*stg, state, inference, logger, owner))
                        return PropagatorState::Enable;

                    propagate_default_product<Hint_>(*data, modulus_r, state, inference, logger, owner);
                } while (inference.did_anything_since_last_call_inside_propagator());

                // Idempotent: the do-while ran the stages (and the default product)
                // to quiescence, so an immediate re-run is one no-op pass (see
                // multiply.cc for the same argument). The mid-loop return above is
                // the contradiction path and its state is ignored.
                return PropagatorState::EnableButIdempotent;
            },
            triggers);

        // Tabulation for GAC: enumerate the distinct underlying variables and
        // the auxiliary slot, so a complete assignment fixes x, y, q and r and
        // every rejected leaf refutes against this block by unit propagation
        // alone.
        TabulationVariables enum_vars;
        auto px = ax.var ? optional{enum_vars.position_of(*ax.var)} : nullopt;
        auto py = ay.var ? optional{enum_vars.position_of(*ay.var)} : nullopt;
        auto pout = aout.var ? optional{enum_vars.position_of(*aout.var)} : nullopt;
        // The divide path materialises no remainder in the proof (cake's rem_* rows range
        // x - w directly, and a rejected (x, y, q) leaf pins magq/absy/w by unit propagation
        // from the assigned q, y so the rem rows refute a wrong remainder), so it enumerates
        // only x, y and q, with no remainder aux and no determined slots. The modulus path
        // enumerates the quotient MAGNITUDE aux |q|; the signed quotient is recovered as
        // sign(x)sign(y)|q| (a magnitude 0 keeps sign 0).
        std::size_t paux = 0;
        if (! expose_quotient)
            paux = enum_vars.position_of(aux);

        auto recover_q = [](Integer auxv, Integer xv, Integer yv) -> Integer { return ((xv >= 0_i) != (yv >= 0_i)) ? -auxv : auxv; };

        // x is a function of the others, pinned by unit propagation forwards
        // through the stages -- but only on the modulus path (divide has no
        // aux to enumerate) and only when x has a fixed sign (for x spanning
        // zero, r = 0 leaves x = +/-|q||y| ambiguous). Its sign then fixes
        // the product's sign: x = sign(x)|q||y| + r. q is a function of the
        // others too, but recovering it means going backwards through the
        // multiplication, which unit propagation cannot do; and y is not a
        // function at all, since q = 0 leaves it anywhere bigger than the
        // remainder. Aliasing spoils the argument, so only distinct slots
        // are claimed.
        vector<DeterminedVariable> determined;
        if (! expose_quotient && pout && pout != px && pout != py)
            determined.push_back({*aout.var, [ax, ay, aout, px, py, paux, recover_q](const vector<Integer> & vals) -> optional<Integer> {
                                      auto xv = px ? ax.coeff * vals[*px] + ax.offset : ax.offset;
                                      auto yv = py ? ay.coeff * vals[*py] + ay.offset : ay.offset;
                                      auto want = xv - recover_q(vals[paux], xv, yv) * yv;
                                      if ((want - aout.offset) % aout.coeff != 0_i)
                                          return nullopt;
                                      return (want - aout.offset) / aout.coeff;
                                  }});
        bool x_fixed_sign = xlo >= 0_i || xhi <= 0_i;
        Integer x_sign = xhi <= 0_i ? -1_i : 1_i;
        if (! expose_quotient && px && px != py && px != pout && x_fixed_sign)
            determined.push_back({*ax.var, [ax, ay, py, pout, paux, aout, x_sign](const vector<Integer> & vals) -> optional<Integer> {
                                      auto yv = py ? ay.coeff * vals[*py] + ay.offset : ay.offset;
                                      auto outv = pout ? aout.coeff * vals[*pout] + aout.offset : aout.offset;
                                      auto want = x_sign * vals[paux] * (yv < 0_i ? -yv : yv) + outv;
                                      if ((want - ax.offset) % ax.coeff != 0_i)
                                          return nullopt;
                                      return (want - ax.offset) / ax.coeff;
                                  }});

        if (want_tabulation(level, enum_vars.vars(), determined, initial_state)) {
            auto accept = [ax, ay, aout, px, py, pout, paux, expose_quotient, recover_q](const vector<Integer> & vals) -> bool {
                auto xv = px ? ax.coeff * vals[*px] + ax.offset : ax.offset;
                auto yv = py ? ay.coeff * vals[*py] + ay.offset : ay.offset;
                auto outv = pout ? aout.coeff * vals[*pout] + aout.offset : aout.offset;
                // Divide enumerates no remainder aux: q is the exposed slot and the
                // remainder is derived. Modulus's aux is the quotient magnitude.
                if (expose_quotient)
                    return is_in_relation(xv, yv, outv, xv - outv * yv);
                return is_in_relation(xv, yv, recover_q(vals[paux], xv, yv), outv);
            };

            install_tabulation<Hint_>(propagators, owner, enum_vars.vars(), move(determined), nullopt, accept, expose_quotient ? "divtab" : "modtab",
                expose_quotient ? "building GAC table for division" : "building GAC table for modulus");
        }
    }
}

Divide::Divide(IntegerVariableID x, IntegerVariableID y, IntegerVariableID quotient) : _x(x), _y(y), _quotient(quotient)
{
}

auto Divide::with_consistency(DivideConsistency level) -> Divide &
{
    _level = level;
    return *this;
}

auto Divide::clone() const -> unique_ptr<Constraint>
{
    auto cloned = make_unique<Divide>(_x, _y, _quotient);
    cloned->with_consistency(_level);
    return cloned;
}

auto Divide::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    install_divide_modulus<hints::Divide>(constraint_id(), true, _x, _y, _quotient, _level, propagators, initial_state, optional_model);
}

auto Divide::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    // Flat primitive shape `(id divide x y quotient)`, matching cake_pb_cp.
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom("divide"), tracker.s_expr_term_of(_x), tracker.s_expr_term_of(_y),
        tracker.s_expr_term_of(_quotient)});
}

Modulus::Modulus(IntegerVariableID x, IntegerVariableID y, IntegerVariableID remainder) : _x(x), _y(y), _remainder(remainder)
{
}

auto Modulus::with_consistency(ModulusConsistency level) -> Modulus &
{
    _level = level;
    return *this;
}

auto Modulus::clone() const -> unique_ptr<Constraint>
{
    auto cloned = make_unique<Modulus>(_x, _y, _remainder);
    cloned->with_consistency(_level);
    return cloned;
}

auto Modulus::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    install_divide_modulus<hints::Modulus>(constraint_id(), false, _x, _y, _remainder, _level, propagators, initial_state, optional_model);
}

auto Modulus::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    // Flat primitive shape `(id modulus x y remainder)`, matching cake_pb_cp.
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom("modulus"), tracker.s_expr_term_of(_x), tracker.s_expr_term_of(_y),
        tracker.s_expr_term_of(_remainder)});
}
