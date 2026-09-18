#include <gcs/constraints/innards/arithmetic_utils.hh>
#include <gcs/constraints/plus_minus/gac.hh>
#include <gcs/constraints/plus_minus/hints.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/large_domain_guard.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>
#include <gcs/interval_set.hh>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdlib>
#include <iterator>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::array;
using std::holds_alternative;
using std::make_shared;
using std::max;
using std::optional;
using std::pair;
using std::prev;
using std::size_t;
using std::vector;
using std::ranges::sort;
using std::ranges::upper_bound;

/*
 * The consistency::GAC arm of Plus and Minus.
 *
 * The row is c_a * a + c_b * b + c_r * result == 0, with every coefficient
 * +1 or -1: (1, 1, -1) for Plus and (1, -1, -1) for Minus. Solving it for any
 * one variable X gives X as a signed sum of the other two, so the values of X
 * with a support are a Minkowski sum of the other two domains, each possibly
 * negated. The propagator removes whatever of dom(X) that sum misses, one
 * infer_not_in_range per maximal run, for result, then a, then b.
 *
 * The consistency::Dynamic arm is the same propagator with a limit on how
 * many pairs of intervals one step may combine; past it the step combines
 * each operand with the other's hull instead. See install_plus_minus_gac().
 *
 * One pass is the GAC fixpoint when the three variables are distinct. Each
 * step reads the domains as the steps before it left them, so take any value
 * still in dom(result) after the first step: it has a support (a', b') in
 * the domains that step read. The second step keeps a' because result' - b'
 * is in its support set, and the third keeps b' because result' - a' is in
 * its. The same argument from the second and third steps' own survivors
 * covers a and b. Aliasing is the exception -- dom(x) read as one operand is
 * not refreshed when x is pruned as another -- so with any two positions
 * sharing a variable the pass repeats until it changes nothing, as the bounds
 * propagator's does.
 *
 * The proof. Removing a run [lo, hi] from X, split on the intervals
 * [yl_i, yh_i] of one of the other two variables, Y, and let Z be the third.
 * The Z values that would support X in [lo, hi] with Y in the i-th interval
 * form a window W_i, which contains no value of Z (that is why the run was
 * removed). So W_i lies below lb(Z), above ub(Z), or inside a single hole
 * [zx, zy] of Z. Each lemma below is one of the six bound rules of the
 * bounds propagator, stated at an interval's endpoints instead of at the
 * domain's bounds: a `pol` of one half of the sum line plus the defining line
 * of one bound atom per non-constant variable, each chosen so that the
 * variable's terms cancel, then saturated into a clause.
 *
 * The conclusion's own RUP then walks Y upwards by unit propagation. From
 * Y >= yl_i, one lemma puts Z at or past the near edge of W_i's hole, Z's
 * hole literal in the reason steps it over the hole, a second lemma pushes Y
 * past yh_i, and Y's hole literal steps it to yl_{i+1}. Windows move
 * monotonically as i increases, so those outside Z's bounds form a prefix and
 * a suffix, which need one lemma each however many intervals they span. A
 * removed run therefore costs at most two lines per interval of Y whose
 * window falls in a hole of Z, plus two, whatever its width.
 *
 * The atoms the lemmas use are exactly the reason's: Y's and Z's bounds and
 * the endpoints of their holes, all taken from the same copy of the domains
 * the support set was computed from. That is what lets the walk run without
 * any link between two order atoms of one variable, and why the reason is
 * built from that copy rather than materialised later: within one pass the
 * domains can move between the step that reads them and a later inference.
 */

namespace
{
    using Intervals = vector<pair<Integer, Integer>>;

    struct Operand
    {
        IntegerVariableID var;
        Integer coeff;
    };

    using Operands = array<Operand, 3>;
    using SumLines = pair<optional<ProofLine>, optional<ProofLine>>;

    // Buffers reused from call to call, so that a wake allocates nothing once
    // they have grown to the domains' interval counts. Held by shared_ptr in the
    // propagator, as ExtensionalData holds its bitmaps, and for the same reason.
    struct Scratch
    {
        Intervals x, o1, o2, o1_hull, o2_hull, pieces, supported;
    };

    auto fill_intervals(Intervals & out, const IntervalSet<Integer> & set) -> void
    {
        out.clear();
        set.for_each_interval([&](Integer lo, Integer hi) { out.emplace_back(lo, hi); });
    }

    // {sp * p + sq * q : p in P, q in Q} for signs sp and sq, as the union of
    // one interval per pair of intervals, sorted and merged into `out`. The cost
    // is the number of pairs, however wide each interval is. Each side is walked
    // in its own ascending order after the sign is applied, so when either side
    // is a single interval the pieces come out sorted already.
    auto signed_sum(Intervals & out, Intervals & pieces, const Intervals & p, Integer sp, const Intervals & q, Integer sq) -> void
    {
        auto oriented = [](const Intervals & v, size_t i, Integer s) {
            return s == 1_i ? v[i] : pair{-v[v.size() - 1 - i].second, -v[v.size() - 1 - i].first};
        };

        LargeDomainIterationCounter guard{"the interval pairs one Plus/Minus GAC support set combined"};
        pieces.clear();
        for (size_t i = 0; i < p.size(); ++i) {
            auto [pl, ph] = oriented(p, i, sp);
            for (size_t j = 0; j < q.size(); ++j) {
                guard.step();
                auto [ql, qh] = oriented(q, j, sq);
                pieces.emplace_back(pl + ql, ph + qh);
            }
        }

        if (p.size() > 1 && q.size() > 1)
            sort(pieces);

        out.clear();
        auto cur = pieces.front();
        for (auto it = pieces.begin() + 1; it != pieces.end(); ++it) {
            if (it->first <= cur.second + 1_i)
                cur.second = max(cur.second, it->second);
            else {
                out.push_back(cur);
                cur = *it;
            }
        }
        out.push_back(cur);
    }

    // Call f(lo, hi) for each maximal run of values in `from` that is not in
    // `minus`, ascending; both are sorted, disjoint, and non-adjacent. The same
    // merge as IntervalSet::each_interval_minus, without the coroutine frame.
    template <typename F_>
    auto for_each_run_minus(const Intervals & from, const Intervals & minus, F_ && f) -> void
    {
        auto j = minus.begin();
        for (const auto & [lo, hi] : from) {
            auto cur = lo;
            while (j != minus.end() && j->second < cur)
                ++j;
            while (j != minus.end() && j->first <= hi) {
                if (j->first > cur)
                    f(cur, j->first - 1_i);
                cur = j->second + 1_i;
                if (cur > hi)
                    break;
                ++j;
            }
            if (cur <= hi)
                f(cur, hi);
        }
    }

    // State a domain exactly, as a generic reason would: its bounds and one
    // range condition per hole. A constant says nothing, so contributes nothing.
    auto append_domain_literals(ReasonLiterals & out, const IntegerVariableID & var, const Intervals & intervals) -> void
    {
        if (holds_alternative<ConstantIntegerVariableID>(var))
            return;

        if (intervals.size() == 1 && intervals.front().first == intervals.front().second) {
            out.push_back(var == intervals.front().first);
            return;
        }

        out.push_back(var >= intervals.front().first);
        out.push_back(var <= intervals.back().second);
        LargeDomainIterationCounter guard{"the runs one Plus/Minus GAC reason stated"};
        for (size_t i = 0; i + 1 < intervals.size(); ++i) {
            guard.step();
            out.push_back(not_in_range(var, intervals[i].second + 1_i, intervals[i + 1].first - 1_i));
        }
    }

    // One lemma: the three variables cannot all satisfy their bound conditions.
    // Take the half of the sum line whose coefficients are h = s * c, which says
    // sum h_v * v >= 0; variable v's condition is v <= bound where h_v = 1, and
    // v >= bound where h_v = -1, so that the conditions force sum h_v * v <=
    // sum h_v * bound_v, which the caller has arranged to be negative. Adding
    // each condition's defining line cancels that variable's terms, leaving
    // the negation of the conditions over their atoms; saturation makes it a
    // clause. A constant's terms are part of the half's constant already, and
    // it has no atom, so it takes no defining line.
    auto emit_lemma(ProofLogger & logger, const SumLines & sum_line, Integer s, const Operands & ops, const array<Integer, 3> & bounds) -> void
    {
        auto & tracker = logger.names_and_ids_tracker();
        PolBuilder pol;
        pol.add(s == 1_i ? *sum_line.second : *sum_line.first);

        Integer slack = 0_i;
        for (size_t v = 0; v < 3; ++v) {
            auto h = s * ops[v].coeff;
            slack += h * bounds[v];
            if (holds_alternative<ConstantIntegerVariableID>(ops[v].var))
                continue;
            pol.add_for_literal(tracker, h == 1_i ? ops[v].var < bounds[v] + 1_i : ops[v].var >= bounds[v]);
        }

        // A lemma whose conditions do not contradict the half would saturate
        // into something trivial, and the walk would stall with a rejected RUP
        // far from here. Catch the arithmetic slip instead.
        if (slack >= 0_i)
            throw UnexpectedException{"Plus/Minus GAC: a bound lemma's conditions are consistent with the sum line"};

        pol.saturate().emit(logger, ProofLevel::Temporary);
    }

    // Emit the lemmas that make ~[X in lo..hi] RUP under a reason stating dom(Y)
    // and dom(Z) exactly as y_int and z_int. See the comment at the top of the
    // file for the walk they support.
    auto justify_removal(ProofLogger & logger, const SumLines & sum_line, const Operands & ops, size_t x, size_t y, size_t z, Integer lo, Integer hi,
        const Intervals & y_int, const Intervals & z_int, const PlusMinusProofMutation & mutation) -> void
    {
        // With no sum line there is nothing to resolve against (proofs with no
        // model); the closing RUP stands alone, as it does for the bounds hint.
        if (! sum_line.first || ! sum_line.second)
            return;

        // Testing only: see PlusMinusProofMutation.
        if (holds_alternative<plus_minus_proof_mutation::OmitLemmas>(mutation))
            return;

        // Z = gamma_x * X + gamma_y * Y, from the row.
        auto gamma_x = -ops[z].coeff * ops[x].coeff;
        auto gamma_y = -ops[z].coeff * ops[y].coeff;
        auto gx_min = gamma_x == 1_i ? lo : -hi;
        auto gx_max = gamma_x == 1_i ? hi : -lo;
        auto window = [&](const pair<Integer, Integer> & yi) -> pair<Integer, Integer> {
            return gamma_y == 1_i ? pair{gx_min + yi.first, gx_max + yi.second} : pair{gx_min - yi.second, gx_max - yi.first};
        };

        // With gamma_y = 1 the windows move up as Y does, so the prefix is the
        // run of windows below lb(Z) and the suffix those above ub(Z); with
        // gamma_y = -1 it is the other way round.
        bool up = gamma_y == 1_i;
        auto z_lb = z_int.front().first, z_ub = z_int.back().second;
        auto below = [&](const pair<Integer, Integer> & w) { return w.second < z_lb; };
        auto above = [&](const pair<Integer, Integer> & w) { return w.first > z_ub; };
        auto in_prefix = [&](const pair<Integer, Integer> & w) { return up ? below(w) : above(w); };
        auto in_suffix = [&](const pair<Integer, Integer> & w) { return up ? above(w) : below(w); };

        // The two lemma shapes. Past Y's lower bound y_lo, Z is pushed to or past
        // b_z: the condition on Y is Y >= y_lo, so s = -c_Y. Past Z's bound b_z,
        // Y is pushed past y_hi: the condition on Y is Y <= y_hi, so s = c_Y.
        // X's condition is whichever bound of the run the chosen half wants,
        // both of which the conclusion's negation supplies.
        auto lemma = [&](Integer s, Integer b_y, Integer b_z) {
            array<Integer, 3> bounds{0_i, 0_i, 0_i};
            bounds[x] = s * ops[x].coeff == 1_i ? hi : lo;
            bounds[y] = b_y;
            bounds[z] = b_z;
            emit_lemma(logger, sum_line, s, ops, bounds);
        };
        auto push_z = [&](Integer y_lo, Integer b_z) { lemma(-ops[y].coeff, y_lo, b_z); };
        auto push_y = [&](Integer y_hi, Integer b_z) { lemma(ops[y].coeff, y_hi, b_z); };

        auto k = y_int.size();
        size_t first_interior = 0;
        while (first_interior < k && in_prefix(window(y_int[first_interior])))
            ++first_interior;
        auto suffix_start = k;
        while (suffix_start > first_interior && in_suffix(window(y_int[suffix_start - 1])))
            --suffix_start;

        // The prefix: Z's own bound pushes Y past the whole prefix at once.
        if (first_interior > 0)
            push_y(y_int[first_interior - 1].second, up ? z_lb : z_ub);

        for (auto i = first_interior; i < suffix_start; ++i) {
            if (holds_alternative<plus_minus_proof_mutation::OmitHoleLemmas>(mutation))
                break;

            auto w = window(y_int[i]);
            // The hole holding the window: the gap before the first interval of
            // Z that starts above the window's low end.
            auto next = upper_bound(z_int, w.first, {}, &pair<Integer, Integer>::first);
            if (next == z_int.begin() || next == z_int.end() || prev(next)->second >= w.first || next->first <= w.second)
                throw UnexpectedException{"Plus/Minus GAC: a removed run has a window that meets the other variable's domain"};
            auto zx = prev(next)->second + 1_i, zy = next->first - 1_i;

            // Into the hole from Y's side, then out past yh_i from the far side.
            push_z(y_int[i].first, up ? zx - 1_i : zy + 1_i);
            push_y(y_int[i].second, up ? zy + 1_i : zx - 1_i);
        }

        // The suffix: from Y at the start of it, Z would pass its own far bound.
        if (suffix_start < k)
            push_z(y_int[suffix_start].first, up ? z_ub : z_lb);
    }

    template <typename Hint_>
    auto propagate_gac(const Operands & ops, bool aliased, const optional<size_t> & max_interval_pairs, Scratch & scratch, const State & state,
        auto & inference, ProofLogger * const logger, const SumLines & sum_line, const ConstraintID & owner, const PlusMinusProofMutation & mutation)
        -> PropagatorState
    {
        // Prune X to what o1_list and o2_list can sum to, each list being
        // either that operand's intervals or its hull. The reason and the
        // lemmas are built from the same lists, which is all the proof needs:
        // a hull just has no holes for a window to fall into.
        auto prune_with = [&](size_t x, size_t o1, size_t o2, const Intervals & o1_list, const Intervals & o2_list) {
            // X = -c_X * (c_o1 * o1 + c_o2 * o2), so this is every value of X
            // with a support.
            signed_sum(scratch.supported, scratch.pieces, o1_list, -ops[x].coeff * ops[o1].coeff, o2_list, -ops[x].coeff * ops[o2].coeff);

            // The proof walks one of the other two a whole interval at a time;
            // walk whichever has fewer.
            bool o1_walks = o1_list.size() <= o2_list.size();
            auto y = o1_walks ? o1 : o2, z = o1_walks ? o2 : o1;
            const auto & y_int = o1_walks ? o1_list : o2_list;
            const auto & z_int = o1_walks ? o2_list : o1_list;

            // scratch.x is a copy, so the inferences below cannot disturb the walk.
            for_each_run_minus(scratch.x, scratch.supported, [&](Integer lo, Integer hi) {
                if (inference.want_reasons()) {
                    ReasonLiterals reason;
                    append_domain_literals(reason, ops[y].var, y_int);
                    if (holds_alternative<plus_minus_proof_mutation::DropWindowHoles>(mutation))
                        append_domain_literals(reason, ops[z].var, Intervals{{z_int.front().first, z_int.back().second}});
                    else
                        append_domain_literals(reason, ops[z].var, z_int);
                    inference.infer_not_in_range(logger, ops[x].var, lo, hi,
                        JustifyExplicitly{
                            [&](const ReasonLiterals &) { justify_removal(*logger, sum_line, ops, x, y, z, lo, hi, y_int, z_int, mutation); },
                            ThenRUP::Yes, Hint_{owner}},
                        ExplicitReason{std::move(reason)});
                }
                else
                    inference.infer_not_in_range(logger, ops[x].var, lo, hi, JustifyUsingRUP{}, NoReason{});
            });
        };

        bool fell_back = false;
        auto prune = [&](size_t x, size_t o1, size_t o2) {
            fill_intervals(scratch.x, state.copy_of_values(ops[x].var));
            fill_intervals(scratch.o1, state.copy_of_values(ops[o1].var));
            fill_intervals(scratch.o2, state.copy_of_values(ops[o2].var));

            if (! max_interval_pairs || scratch.o1.size() * scratch.o2.size() <= *max_interval_pairs) {
                prune_with(x, o1, o2, scratch.o1, scratch.o2);
                return;
            }

            // Too many pairs to combine exactly: combine each operand's
            // intervals with the other's hull instead, once each way round.
            // That costs the sum of the interval counts, and still removes
            // whatever falls between one operand's intervals by more than
            // the other's whole range can bridge.
            fell_back = true;
            scratch.o1_hull.assign({{scratch.o1.front().first, scratch.o1.back().second}});
            scratch.o2_hull.assign({{scratch.o2.front().first, scratch.o2.back().second}});
            prune_with(x, o1, o2, scratch.o1, scratch.o2_hull);
            fill_intervals(scratch.x, state.copy_of_values(ops[x].var));
            prune_with(x, o1, o2, scratch.o1_hull, scratch.o2);
        };

        auto pass = [&]() {
            prune(2, 0, 1);
            prune(0, 2, 1);
            prune(1, 2, 0);
        };

        // One exact pass is the fixpoint for distinct variables. Anything else
        // -- an aliased position, or a step that fell back -- repeats the pass
        // until it changes nothing, as the bounds propagator does.
        while (true) {
            auto before = inference.count_inferences();
            fell_back = false;
            pass();
            if (inference.count_inferences() == before || ! (aliased || fell_back))
                break;
        }

        return PropagatorState::EnableButIdempotent;
    }
}

auto gcs::innards::default_interval_pairs_threshold() -> size_t
{
    static const size_t threshold = []() -> size_t {
        if (const char * e = std::getenv("GCS_INTERVAL_PAIRS_THRESHOLD"))
            return std::strtoull(e, nullptr, 10);
        return 1024; // see the header
    }();
    return threshold;
}

auto gcs::innards::install_plus_minus_gac(Propagators & propagators, const ConstraintID & owner, PlusMinusRow row, IntegerVariableID a,
    IntegerVariableID b, IntegerVariableID result, const SumLines & sum_line, optional<size_t> max_interval_pairs, PlusMinusProofMutation mutation)
    -> void
{
    Operands ops{Operand{a, 1_i}, Operand{b, row == PlusMinusRow::Plus ? 1_i : -1_i}, Operand{result, -1_i}};

    // Positions sharing an underlying variable: see the comment at the top.
    auto va = affine_of(a).var, vb = affine_of(b).var, vr = affine_of(result).var;
    bool aliased = (va && (va == vb || va == vr)) || (vb && vb == vr);

    Triggers triggers;
    triggers.on_change = {a, b, result};

    auto scratch = make_shared<Scratch>();
    if (row == PlusMinusRow::Plus)
        propagators.install(
            owner,
            [ops, aliased, max_interval_pairs, scratch, sum_line, owner, mutation](
                const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                return propagate_gac<hints::PlusNotInRange>(
                    ops, aliased, max_interval_pairs, *scratch, state, inference, logger, sum_line, owner, mutation);
            },
            triggers);
    else
        propagators.install(
            owner,
            [ops, aliased, max_interval_pairs, scratch, sum_line, owner, mutation](
                const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                return propagate_gac<hints::MinusNotInRange>(
                    ops, aliased, max_interval_pairs, *scratch, state, inference, logger, sum_line, owner, mutation);
            },
            triggers);
}
