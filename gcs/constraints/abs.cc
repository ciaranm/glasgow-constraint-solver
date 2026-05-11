#include <gcs/constraints/abs.hh>
#include <gcs/constraints/abs/justify.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/interval_set.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <algorithm>
#include <optional>
#include <sstream>
#include <utility>
#include <vector>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using namespace gcs;
using namespace gcs::innards;

using std::holds_alternative;
using std::max;
using std::min;
using std::pair;
using std::ranges::sort;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
#endif

namespace
{
    // Collect a set of (lower, upper) pieces (possibly unordered and
    // overlapping) into an IntervalSet via insert_at_end. Linear sort +
    // merge; small for the dominant single-interval cases.
    auto pieces_to_set(vector<pair<Integer, Integer>> & pieces) -> IntervalSet<Integer>
    {
        IntervalSet<Integer> result;
        if (pieces.empty())
            return result;

        sort(pieces);
        auto cur = pieces.front();
        for (auto it = pieces.begin() + 1; it != pieces.end(); ++it) {
            if (it->first <= cur.second + 1_i)
                cur.second = max(cur.second, it->second);
            else {
                result.insert_at_end(cur.first, cur.second);
                cur = *it;
            }
        }
        result.insert_at_end(cur.first, cur.second);
        return result;
    }
}

Abs::Abs(const IntegerVariableID v1, const IntegerVariableID v2) :
    _v1(v1),
    _v2(v2)
{
}

auto Abs::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Abs>(_v1, _v2);
}

auto Abs::install(Propagators & propagators, State &, ProofModel * const optional_model) && -> void
{
    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto Abs::define_proof_model(ProofModel & model) -> void
{
    _abs_nonneg_lines = model.add_constraint("Abs", "non-negative", WPBSum{} + 1_i * _v2 + -1_i * _v1 == 0_i, HalfReifyOnConjunctionOf{_v1 >= 0_i});
    _abs_neg_lines = model.add_constraint("Abs", "negative", WPBSum{} + 1_i * _v2 + 1_i * _v1 == 0_i, HalfReifyOnConjunctionOf{_v1 < 0_i});
}

auto Abs::install_propagators(Propagators & propagators) -> void
{
    // All four consequence bounds live in a single SimpleDefinition-priority
    // initialiser. The OPB encoding stays free of "Abs" labels for inferences
    // that aren't definitional; each bound's proof is assembled via the
    // shared helpers in abs/justify.hh as PB resolution steps over the
    // encoding's two half-reified halves.
    //
    // VeriPB's RUP alone cannot derive any of these bounds for non-constant
    // v1, because it can't case-split on `v1 >= 0 \/ v1 < 0`. The helpers
    // supply the case split explicitly; the final RUP then closes the
    // inference. When v1 IS constant the encoding's relevant half is
    // unreified, the helpers short-circuit, and plain RUP suffices. When v2
    // is constant we bail out -- the propagator's per-value loop will
    // discover any UNSAT.
    propagators.install_initialiser(
        [v1 = _v1, v2 = _v2,
            abs_nonneg_le = _abs_nonneg_lines.first,
            abs_nonneg_ge = _abs_nonneg_lines.second,
            abs_neg_le = _abs_neg_lines.first,
            abs_neg_ge = _abs_neg_lines.second](
            State & state, auto & inference, ProofLogger * const logger) -> void {
            if (holds_alternative<ConstantIntegerVariableID>(v2))
                return;

            inference.infer(logger, v2 >= 0_i,
                JustifyExplicitlyThenRUP{
                    [logger, v1, v2, abs_nonneg_ge](const ReasonFunction &) -> void {
                        justify_abs_v2_ge_zero(*logger, v1, v2, *abs_nonneg_ge);
                    }},
                ReasonFunction{});

            auto v2_ub = state.upper_bound(v2);

            // Skip when ub(v2) < 0 -- the v1_ge_(ub(v2)+1) flag would
            // collide with v1_ge0 / become vacuous; the propagator detects
            // UNSAT directly.
            if (v2_ub >= 0_i) {
                inference.infer(logger, v1 < v2_ub + 1_i,
                    JustifyExplicitlyThenRUP{
                        [logger, v1, v2, v2_ub, abs_nonneg_ge](const ReasonFunction & r) -> void {
                            justify_abs_v1_le_v2_ub(*logger, v1, v2, v2_ub, *abs_nonneg_ge, r);
                        }},
                    ReasonFunction{});
            }

            // Symmetric flag-collision concern: skip when ub(v2) <= 0.
            if (v2_ub > 0_i) {
                inference.infer(logger, v1 >= -v2_ub,
                    JustifyExplicitlyThenRUP{
                        [logger, v1, v2, v2_ub, abs_neg_ge](const ReasonFunction & r) -> void {
                            justify_abs_v1_ge_neg_v2_ub(*logger, v1, v2, v2_ub, *abs_neg_ge, r);
                        }},
                    ReasonFunction{});
            }

            auto [v1_lb, v1_ub] = state.bounds(v1);
            auto big_m = max(v1_ub, -v1_lb);
            inference.infer(logger, v2 < big_m + 1_i,
                JustifyExplicitlyThenRUP{
                    [logger, v1, v2, v1_lb, v1_ub, big_m, abs_nonneg_le, abs_neg_le](const ReasonFunction & r) -> void {
                        justify_abs_v2_le_big_m(*logger, v1, v2, v1_lb, v1_ub, big_m, *abs_nonneg_le, *abs_neg_le, r);
                    }},
                ReasonFunction{});
        },
        InitialiserPriority::SimpleDefinition);

    // Propagator: v2 = abs(v1). Reasons over v1's image (under abs) and
    // v2's preimage. Contiguous-domain cases collapse to a handful of bound
    // updates with O(1) proof lines; interior holes still need per-value
    // pruning, but the iteration is over gaps, not values.
    Triggers triggers{.on_change = {_v1, _v2}};
    propagators.install(
        [v1 = _v1, v2 = _v2,
            abs_nonneg_le = _abs_nonneg_lines.first,
            abs_nonneg_ge = _abs_nonneg_lines.second,
            abs_neg_le = _abs_neg_lines.first,
            abs_neg_ge = _abs_neg_lines.second](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            auto v1_set = state.copy_of_values(v1);
            auto v2_set = state.copy_of_values(v2);
            auto [v1_lb, v1_ub] = state.bounds(v1);
            auto [v2_lb, v2_ub] = state.bounds(v2);
            auto v2_is_constant = holds_alternative<ConstantIntegerVariableID>(v2);

            // Direction v1 -> v2: tighten v2 from the image of v1. Skipped
            // when v2 is constant -- the proof helpers need v2's order-encoding
            // flags, which don't exist for constants; per-value pruning below
            // detects any UNSAT directly.
            //
            // image_ub = max(|v1_lb|, v1_ub). image_lb = lb(v1) when v1 is
            // entirely positive, -ub(v1) when entirely negative, and 0
            // otherwise (already established by the initialiser).
            if (! v2_is_constant) {
                auto image_ub = max(-v1_lb, v1_ub);
                if (image_ub < v2_ub) {
                    inference.infer_less_than(logger, v2, image_ub + 1_i,
                        JustifyExplicitlyThenRUP{
                            [logger, v1, v2, v1_lb, v1_ub, image_ub, abs_nonneg_le, abs_neg_le](const ReasonFunction & r) -> void {
                                justify_abs_v2_le_big_m(*logger, v1, v2, v1_lb, v1_ub, image_ub, *abs_nonneg_le, *abs_neg_le, r);
                            }},
                        ReasonFunction{[v1, v1_lb, v1_ub]() { return Reason{{v1 >= v1_lb, v1 < v1_ub + 1_i}}; }});
                }

                if (v1_lb >= 1_i && v1_lb > v2_lb) {
                    inference.infer_greater_than_or_equal(logger, v2, v1_lb,
                        JustifyExplicitlyThenRUP{
                            [logger, v1, v2, v1_lb, abs_nonneg_ge](const ReasonFunction & r) -> void {
                                justify_abs_v2_lb(*logger, v1, v2, AbsLbSide::Nonneg, v1_lb, *abs_nonneg_ge, r);
                            }},
                        ReasonFunction{[v1, v1_lb]() { return Reason{v1 >= v1_lb}; }});
                }
                else if (v1_ub <= -1_i && -v1_ub > v2_lb) {
                    inference.infer_greater_than_or_equal(logger, v2, -v1_ub,
                        JustifyExplicitlyThenRUP{
                            [logger, v1, v2, v1_ub, abs_neg_ge](const ReasonFunction & r) -> void {
                                justify_abs_v2_lb(*logger, v1, v2, AbsLbSide::Nonpos, -v1_ub, *abs_neg_ge, r);
                            }},
                        ReasonFunction{[v1, v1_ub]() { return Reason{v1 < v1_ub + 1_i}; }});
                }
            }

            // Direction v2 -> v1: tighten v1 from the preimage of v2.
            if (v2_ub < v1_ub) {
                inference.infer_less_than(logger, v1, v2_ub + 1_i,
                    JustifyExplicitlyThenRUP{
                        [logger, v1, v2, v2_ub, abs_nonneg_ge](const ReasonFunction & r) -> void {
                            justify_abs_v1_le_v2_ub(*logger, v1, v2, v2_ub, *abs_nonneg_ge, r);
                        }},
                    ReasonFunction{[v2, v2_ub]() { return Reason{v2 < v2_ub + 1_i}; }});
            }
            if (-v2_ub > v1_lb) {
                inference.infer_greater_than_or_equal(logger, v1, -v2_ub,
                    JustifyExplicitlyThenRUP{
                        [logger, v1, v2, v2_ub, abs_neg_ge](const ReasonFunction & r) -> void {
                            justify_abs_v1_ge_neg_v2_ub(*logger, v1, v2, v2_ub, *abs_neg_ge, r);
                        }},
                    ReasonFunction{[v2, v2_ub]() { return Reason{v2 < v2_ub + 1_i}; }});
            }

            // Interior pruning: remove values in v2 with no preimage in v1,
            // and values in v1 whose abs is not in v2. Walk gaps via
            // each_interval_minus, then per-value within the now-tightened
            // bounds.

            vector<pair<Integer, Integer>> image_pieces;
            for (auto [a, b] : v1_set.each_interval()) {
                if (a >= 0_i)
                    image_pieces.emplace_back(a, b);
                else if (b < 0_i)
                    image_pieces.emplace_back(-b, -a);
                else
                    image_pieces.emplace_back(0_i, max(-a, b));
            }
            auto image_set = pieces_to_set(image_pieces);

            auto [post_v2_lb, post_v2_ub] = state.bounds(v2);
            for (auto [lo, hi] : v2_set.each_interval_minus(image_set)) {
                auto clipped_lo = max(lo, post_v2_lb);
                auto clipped_hi = min(hi, post_v2_ub);
                for (Integer val = clipped_lo; val <= clipped_hi; ++val) {
                    if (! state.in_domain(v2, val))
                        continue;
                    inference.infer_not_equal(logger, v2, val,
                        JustifyExplicitlyThenRUP{[logger, v1, v2, val](const ReasonFunction & r) {
                            justify_abs_hole(*logger, r, v1, v2, val);
                        }},
                        ReasonFunction{[v1, val]() { return Reason{{v1 != val, v1 != -val}}; }});
                }
            }

            vector<pair<Integer, Integer>> preimage_pieces;
            for (auto [a, b] : v2_set.each_interval()) {
                if (a == 0_i)
                    preimage_pieces.emplace_back(-b, b);
                else {
                    preimage_pieces.emplace_back(-b, -a);
                    preimage_pieces.emplace_back(a, b);
                }
            }
            auto preimage_set = pieces_to_set(preimage_pieces);

            auto [post_v1_lb, post_v1_ub] = state.bounds(v1);
            for (auto [lo, hi] : v1_set.each_interval_minus(preimage_set)) {
                auto clipped_lo = max(lo, post_v1_lb);
                auto clipped_hi = min(hi, post_v1_ub);
                for (Integer val = clipped_lo; val <= clipped_hi; ++val) {
                    if (! state.in_domain(v1, val))
                        continue;
                    inference.infer_not_equal(logger, v1, val, JustifyUsingRUP{},
                        ReasonFunction{[v2, val]() { return Reason{v2 != abs(val)}; }});
                }
            }

            return PropagatorState::Enable;
        },
        triggers);
}

auto Abs::s_exprify(const string & name, const innards::ProofModel * const model) const -> string
{
    stringstream s;

    print(s, "{} abs", name);
    print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(_v1));
    print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(_v2));

    return s.str();
}
