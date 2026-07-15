#include <gcs/constraints/linear/hints.hh>
#include <gcs/constraints/linear/justify.hh>
#include <gcs/constraints/linear/propagate.hh>
#include <gcs/constraints/linear/utils.hh>
#include <gcs/innards/assertion_hints.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/state.hh>
#include <gcs/innards/variable_id_utils.hh>

#include <util/enumerate.hh>

#include <any>
#include <cstdlib>
#include <sstream>
#include <string>
#include <type_traits>
#include <vector>

using std::is_same_v;
using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::stringstream;
using std::variant;
using std::vector;

using namespace gcs;
using namespace gcs::innards;

namespace
{
    auto negate(Integer v) -> Integer
    {
        return -v;
    }

    auto negate(bool b) -> bool
    {
        return ! b;
    }

    auto get_coeff_or_bool(const PositiveOrNegative<SimpleIntegerVariableID> & cv) -> bool
    {
        return cv.positive;
    }

    auto get_coeff_or_bool(const Weighted<SimpleIntegerVariableID> & cv) -> Integer
    {
        return cv.coefficient;
    }

    auto get_coeff_or_bool(const SimpleIntegerVariableID &) -> bool
    {
        return true;
    }

    auto linear_bounds_reason(bool want_reason, const auto & coeff_vars, const LinearBounds & bounds, const optional<SimpleIntegerVariableID> & var,
        bool invert, const optional<Literal> & add_to_reason) -> Reason
    {
        // Building this reason is O(coeff_vars) and it is only ever read when proofs
        // are on (or conflict-directed search wants it), so skip it otherwise -- on a
        // wide linear constraint that loop runs on every firing during plain search.
        if (! want_reason)
            return NoReason{};

        ReasonLiterals reason;
        for (const auto & [idx, cv] : enumerate(coeff_vars.terms)) {
            if (var && get_var(cv) != *var) {
                if ((get_coeff(cv) < 0_i) != invert) {
                    reason.emplace_back(get_var(cv) <= bounds[idx].second);
                }
                else {
                    reason.emplace_back(get_var(cv) >= bounds[idx].first);
                }
            }
        }

        if (add_to_reason)
            reason.push_back(*add_to_reason);

        return ExplicitReason{reason};
    }

    // Returns false if the inference contradicted: the caller must stop immediately
    // (it may not read state again until backtrack). Uses the non-throwing
    // infer_*_or_stop path so a failure does not unwind via an exception. When an
    // inference fires, the tightened side of bounds[p] is updated in place from the
    // value the operation landed on (upper for a positive coefficient, lower for a
    // negative one) -- the bound can be tighter than requested when it snaps across
    // a hole, and the other side is untouched, so this is exactly the state.bounds()
    // re-read the caller used to do, without the round trip.
    [[nodiscard]] auto infer(auto & inference, ProofLogger * const logger, LinearBounds & bounds, const auto & coeff_vars, int p,
        const SimpleIntegerVariableID & var, Integer remainder, const bool coeff, bool second_constraint_for_equality,
        const optional<pair<optional<ProofLine>, optional<ProofLine>>> & proof_line, const optional<Literal> & add_to_reason, const auto & hint)
        -> bool
    {
        if (coeff) {
            if (bounds[p].second >= (1_i + remainder)) {
                auto justf = [&](const ReasonLiterals &) {
                    justify_linear_bounds(*logger, coeff_vars, bounds, var, second_constraint_for_equality, proof_line.value());
                };
                auto landed =
                    inference.infer_less_than_or_stop_with_updated_bound(logger, var, 1_i + remainder, JustifyExplicitly{justf, ThenRUP::Yes, hint},
                        linear_bounds_reason(inference.want_reasons(), coeff_vars, bounds, var, second_constraint_for_equality, add_to_reason));
                if (! landed)
                    return false;
                bounds[p].second = *landed;
            }
        }
        else {
            if (bounds[p].first < -remainder) {
                auto justf = [&](const ReasonLiterals &) {
                    justify_linear_bounds(*logger, coeff_vars, bounds, var, second_constraint_for_equality, proof_line.value());
                };
                auto landed = inference.infer_greater_than_or_equal_or_stop_with_updated_bound(logger, var, -remainder,
                    JustifyExplicitly{justf, ThenRUP::Yes, hint},
                    linear_bounds_reason(inference.want_reasons(), coeff_vars, bounds, var, second_constraint_for_equality, add_to_reason));
                if (! landed)
                    return false;
                bounds[p].first = *landed;
            }
        }
        return true;
    }

    [[nodiscard]] auto infer(auto & inference, ProofLogger * const logger, LinearBounds & bounds, const auto & coeff_vars, int p,
        const SimpleIntegerVariableID & var, Integer remainder, const Integer coeff, bool second_constraint_for_equality,
        const optional<pair<optional<ProofLine>, optional<ProofLine>>> & proof_line, const optional<Literal> & add_to_reason, const auto & hint)
        -> bool
    {
        // lots of conditionals to get the rounding right... a positive coefficient
        // tightens the upper bound, a negative one the lower; either way bounds[p]'s
        // tightened side is refreshed in place from where the inference landed (see
        // the bool-coefficient overload above).
        if (coeff > 0_i && remainder >= 0_i) {
            if (bounds[p].second >= (1_i + remainder / coeff)) {
                auto justf = [&](const ReasonLiterals &) {
                    justify_linear_bounds(*logger, coeff_vars, bounds, var, second_constraint_for_equality, proof_line.value());
                };
                auto landed = inference.infer_less_than_or_stop_with_updated_bound(logger, var, 1_i + remainder / coeff,
                    JustifyExplicitly{justf, ThenRUP::Yes, hint},
                    linear_bounds_reason(inference.want_reasons(), coeff_vars, bounds, var, second_constraint_for_equality, add_to_reason));
                if (! landed)
                    return false;
                bounds[p].second = *landed;
            }
        }
        else if (coeff > 0_i && remainder < 0_i) {
            auto div_with_rounding = -((-remainder + coeff - 1_i) / coeff);
            if (bounds[p].second >= 1_i + div_with_rounding) {
                auto justf = [&](const ReasonLiterals &) {
                    justify_linear_bounds(*logger, coeff_vars, bounds, var, second_constraint_for_equality, proof_line.value());
                };
                auto landed = inference.infer_less_than_or_stop_with_updated_bound(logger, var, 1_i + div_with_rounding,
                    JustifyExplicitly{justf, ThenRUP::Yes, hint},
                    linear_bounds_reason(inference.want_reasons(), coeff_vars, bounds, var, second_constraint_for_equality, add_to_reason));
                if (! landed)
                    return false;
                bounds[p].second = *landed;
            }
        }
        else if (coeff < 0_i && remainder >= 0_i) {
            if (bounds[p].first < remainder / coeff) {
                auto justf = [&](const ReasonLiterals &) {
                    justify_linear_bounds(*logger, coeff_vars, bounds, var, second_constraint_for_equality, proof_line.value());
                };
                auto landed = inference.infer_greater_than_or_equal_or_stop_with_updated_bound(logger, var, remainder / coeff,
                    JustifyExplicitly{justf, ThenRUP::Yes, hint},
                    linear_bounds_reason(inference.want_reasons(), coeff_vars, bounds, var, second_constraint_for_equality, add_to_reason));
                if (! landed)
                    return false;
                bounds[p].first = *landed;
            }
        }
        else if (coeff < 0_i && remainder < 0_i) {
            auto div_with_rounding = (-remainder + -coeff - 1_i) / -coeff;
            if (bounds[p].first < div_with_rounding) {
                auto justf = [&](const ReasonLiterals &) {
                    justify_linear_bounds(*logger, coeff_vars, bounds, var, second_constraint_for_equality, proof_line.value());
                };
                auto landed = inference.infer_greater_than_or_equal_or_stop_with_updated_bound(logger, var, div_with_rounding,
                    JustifyExplicitly{justf, ThenRUP::Yes, hint},
                    linear_bounds_reason(inference.want_reasons(), coeff_vars, bounds, var, second_constraint_for_equality, add_to_reason));
                if (! landed)
                    return false;
                bounds[p].first = *landed;
            }
        }
        else
            throw UnexpectedException{"uh, trying to divide by zero?"};
        return true;
    }
}

template <typename Hint_>
auto gcs::innards::propagate_linear(const auto & coeff_vars, Integer value, const State & state, auto & inference, ProofLogger * const logger,
    bool equality, const optional<pair<optional<ProofLine>, optional<ProofLine>>> & proof_line, const optional<Literal> & add_to_reason,
    const Hint_ & hint) -> PropagatorState
{
    LinearBounds bounds;
    bounds.reserve(coeff_vars.terms.size());

    // need to check the empty sum case somewhere, because we only get a contradiction
    // by inferring a specific variable has to take a value that it can't
    if (coeff_vars.terms.empty()) {
        if (! (0_i <= value)) {
            inference.contradiction(
                logger, JustifyUsingRUP{hint}, linear_bounds_reason(inference.want_reasons(), coeff_vars, bounds, nullopt, false, add_to_reason));
        }
        return PropagatorState::DisableUntilBacktrack;
    }

    for (const auto & cv : coeff_vars.terms)
        bounds.push_back(state.bounds(get_var(cv)));

    // lower_sum, the least value the (forward) sum can take, from each term's
    // min contribution. It is invariant within a forward sweep -- the sweep
    // writes only upper bounds of positive-coefficient terms and lower bounds
    // of negative ones, neither of which feeds lower_sum -- so one recompute at
    // the top of each sweep from the current bounds is exact, and picks up any
    // tightening a previous inverse sweep made.
    auto compute_lower_sum = [&]() -> Integer {
        Integer s{0};
        for (unsigned i = 0, e = coeff_vars.terms.size(); i != e; ++i) {
            const auto & cv = coeff_vars.terms[i];
            if constexpr (is_same_v<decltype(cv), const SimpleIntegerVariableID &>)
                s += bounds[i].first;
            else if constexpr (is_same_v<decltype(cv), const pair<bool, SimpleIntegerVariableID> &>)
                s += (cv.first ? bounds[i].first : -bounds[i].second);
            else {
                auto coeff = get_coeff(cv);
                s += (coeff >= 0_i) ? (coeff * bounds[i].first) : (coeff * bounds[i].second);
            }
        }
        return s;
    };

    // The forward (sum <= value) sweep reaches the <= fixpoint in one pass and is
    // idempotent on its own: a positive-coefficient term is only ever written on
    // its upper bound and only ever read (via lower_sum) on its lower, and vice
    // versa for negative coefficients, so reads and writes are disjoint per
    // variable and no write -- not even one that snaps past a hole, since removing
    // values above a bound cannot raise a minimum -- can re-enable a guard.
    //
    // An equality additionally runs the inverse (sum >= value) sweep, which reads
    // exactly the upper bounds the forward sweep wrote and writes the lower bounds
    // it read: a closed loop, so the inverse can tighten a bound that lets the
    // forward tighten further. We therefore alternate the two sweeps until neither
    // infers anything, reaching the propagator's own fixpoint in a single call, so
    // it can claim idempotence. Previously the equality left that alternation to
    // the propagation queue's self-requeue (a full re-dispatch, re-reading every
    // bound, per fwd<->inv exchange); the internal loop keeps the bounds snapshot
    // warm and reaches the identical fixpoint (propagators are monotone).
    // Per-sweep change detection lets the loop stop the moment a sweep is clean,
    // rather than always paying one confirming double-sweep: after a clean
    // forward the inverse's inputs (the forward's upper bounds) are unchanged
    // from last time, and after a clean inverse the forward's inputs (the
    // inverse's lower bounds) are, so either clean sweep proves the fixpoint. We
    // detect change with the tracker's non-destructive inference count rather
    // than made_progress_since_last_check(), because that flag
    // is shared with the propagate_stages callers (multiply/divide/power run
    // their own do-while on it across all stages), so clearing it here would
    // corrupt their loop.
    for (bool first = true;; first = false) {
        auto inferences_before_forward = inference.count_inferences();

        Integer lower_sum = compute_lower_sum();
        for (unsigned p = 0, p_end = coeff_vars.terms.size(); p != p_end; ++p) {
            const auto & cv = coeff_vars.terms[p];

            Integer lower_without_me{0_i};
            if constexpr (is_same_v<decltype(cv), const SimpleIntegerVariableID &>)
                lower_without_me = lower_sum - bounds[p].first;
            else if constexpr (is_same_v<decltype(cv), const pair<bool, SimpleIntegerVariableID> &>)
                lower_without_me = lower_sum - (cv.first ? bounds[p].first : -bounds[p].second);
            else
                lower_without_me = lower_sum - ((get_coeff(cv) >= 0_i) ? (get_coeff(cv) * bounds[p].first) : (get_coeff(cv) * bounds[p].second));
            Integer remainder = value - lower_without_me;

            if (! infer(
                    inference, logger, bounds, coeff_vars, p, get_var(cv), remainder, get_coeff_or_bool(cv), false, proof_line, add_to_reason, hint))
                return PropagatorState::Enable; // contradiction: stop before reading the (now junk) state
            // infer() has refreshed bounds[p]'s tightened side in place.
        }

        // A clean forward sweep after the first iteration means the inverse's
        // last output fed the forward nothing new; the fixpoint is reached.
        if (! equality || (! first && inference.count_inferences() == inferences_before_forward))
            break;

        auto inferences_before_inverse = inference.count_inferences();
        Integer inv_lower_sum{0};
        for (const auto & [idx, cv] : enumerate(coeff_vars.terms)) {
            if constexpr (is_same_v<decltype(cv), const SimpleIntegerVariableID &>)
                inv_lower_sum += -bounds[idx].second;
            else {
                auto coeff = get_coeff(cv);
                inv_lower_sum += (-coeff >= 0_i) ? (-coeff * bounds[idx].first) : (-coeff * bounds[idx].second);
            }
        }

        for (unsigned p = 0, p_end = coeff_vars.terms.size(); p != p_end; ++p) {
            const auto & cv = coeff_vars.terms[p];
            Integer inv_lower_without_me{0_i};
            if constexpr (is_same_v<decltype(cv), const SimpleIntegerVariableID &>)
                inv_lower_without_me = inv_lower_sum + bounds[p].second;
            else if constexpr (is_same_v<decltype(cv), const pair<bool, SimpleIntegerVariableID> &>)
                inv_lower_without_me = inv_lower_sum + (! cv.first ? -bounds[p].first : bounds[p].second);
            else
                inv_lower_without_me =
                    inv_lower_sum + ((-get_coeff(cv) >= 0_i) ? (get_coeff(cv) * bounds[p].first) : (get_coeff(cv) * bounds[p].second));

            Integer inv_remainder = -value - inv_lower_without_me;

            if (! infer(inference, logger, bounds, coeff_vars, p, get_var(cv), inv_remainder, negate(get_coeff_or_bool(cv)), true, proof_line,
                    add_to_reason, hint))
                return PropagatorState::Enable; // contradiction: stop before reading the (now junk) state
            // infer() has refreshed bounds[p]'s tightened side in place.

            if constexpr (is_same_v<decltype(cv), const SimpleIntegerVariableID &>)
                inv_lower_sum = inv_lower_without_me - bounds[p].second;
            else if constexpr (is_same_v<decltype(cv), const pair<bool, SimpleIntegerVariableID> &>)
                inv_lower_sum = inv_lower_without_me + (! cv.first ? bounds[p].first : -bounds[p].second);
            else
                inv_lower_sum =
                    inv_lower_without_me + ((-get_coeff(cv) >= 0_i) ? (-get_coeff(cv) * bounds[p].first) : (-get_coeff(cv) * bounds[p].second));
        }

        // A clean inverse sweep means the forward's last output fed the inverse
        // nothing new; the fixpoint is reached.
        if (inference.count_inferences() == inferences_before_inverse)
            break;
    }

    return PropagatorState::EnableButIdempotent;
}

// Two hint instantiations per (coeff-vector type, tracker): hints::LinearEquality
// for the equality propagator, NoHint for the reified-inequality propagators (which
// pass no hint). The hint rides the JustifyExplicitly, so it is materialised lazily
// in assertion mode rather than eagerly at the call site.
#define GCS_INSTANTIATE_PROPAGATE_LINEAR(CoeffVars, Tracker, Hint)                                                                                   \
    template auto gcs::innards::propagate_linear(const CoeffVars & coeff_vars, Integer value, const State & state, Tracker &,                        \
        ProofLogger * const logger, bool equality, const optional<pair<optional<ProofLine>, optional<ProofLine>>> & proof_line,                      \
        const optional<Literal> & add_to_reason, const Hint & hint) -> PropagatorState

GCS_INSTANTIATE_PROPAGATE_LINEAR(SumOf<Weighted<SimpleIntegerVariableID>>, SimpleInferenceTracker, hints::LinearEquality);
GCS_INSTANTIATE_PROPAGATE_LINEAR(SumOf<PositiveOrNegative<SimpleIntegerVariableID>>, SimpleInferenceTracker, hints::LinearEquality);
GCS_INSTANTIATE_PROPAGATE_LINEAR(SumOf<SimpleIntegerVariableID>, SimpleInferenceTracker, hints::LinearEquality);
GCS_INSTANTIATE_PROPAGATE_LINEAR(SumOf<Weighted<SimpleIntegerVariableID>>, EagerProofLoggingInferenceTracker, hints::LinearEquality);
GCS_INSTANTIATE_PROPAGATE_LINEAR(SumOf<PositiveOrNegative<SimpleIntegerVariableID>>, EagerProofLoggingInferenceTracker, hints::LinearEquality);
GCS_INSTANTIATE_PROPAGATE_LINEAR(SumOf<SimpleIntegerVariableID>, EagerProofLoggingInferenceTracker, hints::LinearEquality);

GCS_INSTANTIATE_PROPAGATE_LINEAR(SumOf<Weighted<SimpleIntegerVariableID>>, SimpleInferenceTracker, NoHint);
GCS_INSTANTIATE_PROPAGATE_LINEAR(SumOf<PositiveOrNegative<SimpleIntegerVariableID>>, SimpleInferenceTracker, NoHint);
GCS_INSTANTIATE_PROPAGATE_LINEAR(SumOf<SimpleIntegerVariableID>, SimpleInferenceTracker, NoHint);
GCS_INSTANTIATE_PROPAGATE_LINEAR(SumOf<Weighted<SimpleIntegerVariableID>>, EagerProofLoggingInferenceTracker, NoHint);
GCS_INSTANTIATE_PROPAGATE_LINEAR(SumOf<PositiveOrNegative<SimpleIntegerVariableID>>, EagerProofLoggingInferenceTracker, NoHint);
GCS_INSTANTIATE_PROPAGATE_LINEAR(SumOf<SimpleIntegerVariableID>, EagerProofLoggingInferenceTracker, NoHint);

#undef GCS_INSTANTIATE_PROPAGATE_LINEAR

auto gcs::innards::default_linear_incremental_threshold() -> std::size_t
{
    static const std::size_t threshold = []() -> std::size_t {
        if (const char * e = std::getenv("GCS_LINEAR_INCREMENTAL_THRESHOLD"))
            return std::strtoull(e, nullptr, 10);
        return 8; // default: use the incremental path for constraints with >= 8 terms
    }();
    return threshold;
}

template <typename Hint_>
auto gcs::innards::propagate_linear_incremental(const auto & coeff_vars, Integer value, const State & state, auto & inference,
    ProofLogger * const logger, bool equality, const optional<pair<optional<ProofLine>, optional<ProofLine>>> & proof_line,
    const optional<Literal> & add_to_reason, std::vector<std::size_t> & active, ConstraintStateHandle state_handle, const Hint_ & hint)
    -> PropagatorState
{
    // The empty (all-coefficients-cancelled) constraint has no terms to fold; defer to
    // the stateless propagator, which handles the constant-only feasibility check.
    if (coeff_vars.terms.empty())
        return propagate_linear(coeff_vars, value, state, inference, logger, equality, proof_line, add_to_reason, hint);

    auto & st = std::any_cast<LinearIncrementalState &>(state.get_constraint_state(state_handle));
    const auto n = coeff_vars.terms.size();
    const bool want = inference.want_reasons();

    // Per-tier contributions, specialised exactly as the stateless propagate_linear is,
    // so the inferences (and hence the search tree) are identical -- min for the <= half,
    // -(max) for the >= (inverse) half.
    auto min_contrib = [](const auto & cv, const pair<Integer, Integer> & b) -> Integer {
        using CV = std::decay_t<decltype(cv)>;
        if constexpr (is_same_v<CV, SimpleIntegerVariableID>)
            return b.first;
        else if constexpr (is_same_v<CV, PositiveOrNegative<SimpleIntegerVariableID>>)
            return cv.positive ? b.first : -b.second;
        else {
            auto c = get_coeff(cv);
            return (c >= 0_i) ? (c * b.first) : (c * b.second);
        }
    };
    auto inv_contrib = [](const auto & cv, const pair<Integer, Integer> & b) -> Integer {
        using CV = std::decay_t<decltype(cv)>;
        if constexpr (is_same_v<CV, SimpleIntegerVariableID>)
            return -b.second;
        else if constexpr (is_same_v<CV, PositiveOrNegative<SimpleIntegerVariableID>>)
            return cv.positive ? -b.second : b.first;
        else {
            auto c = get_coeff(cv);
            return (c >= 0_i) ? -(c * b.second) : -(c * b.first);
        }
    };

    // Active terms' bounds are always needed; fixed terms' bounds only when a reason or
    // justification will actually read them (proofs / conflict learning).
    LinearBounds bounds;
    bounds.resize(n, pair{0_i, 0_i});
    for (std::size_t k = 0; k != st.n_active; ++k)
        bounds[active[k]] = state.bounds(get_var(coeff_vars.terms[active[k]]));
    if (want)
        for (std::size_t k = st.n_active; k != n; ++k)
            bounds[active[k]] = state.bounds(get_var(coeff_vars.terms[active[k]]));

    // Alternate the forward (<=) and inverse (>=) sweeps over the active terms
    // to the equality's own fixpoint in a single call, so it can claim
    // idempotence -- see propagate_linear for the read/write reasoning (the
    // inverse writes the lower bounds the forward reads, so it can feed a
    // further forward tightening) and the same non-destructive change detection
    // (the shared progress flag belongs to the propagate_stages callers).
    // lower_sum / inv_lower_sum are invariant within a sweep, so each is
    // recomputed at the sweep top from the current active-term bounds plus the
    // folded fixed_lower. An inequality does a single forward sweep, as before.
    for (bool first = true;; first = false) {
        auto inferences_before_forward = inference.count_inferences();

        // Forward (<=): coeff_p * x_p <= value - (lower_sum - contrib_p).
        Integer lower_sum = st.fixed_lower;
        for (std::size_t k = 0; k != st.n_active; ++k)
            lower_sum += min_contrib(coeff_vars.terms[active[k]], bounds[active[k]]);

        for (std::size_t k = 0; k != st.n_active; ++k) {
            auto p = active[k];
            const auto & cv = coeff_vars.terms[p];
            Integer lower_without_me = lower_sum - min_contrib(cv, bounds[p]);
            Integer remainder = value - lower_without_me;
            if (! infer(
                    inference, logger, bounds, coeff_vars, p, get_var(cv), remainder, get_coeff_or_bool(cv), false, proof_line, add_to_reason, hint))
                return PropagatorState::Enable;
            // infer() has refreshed bounds[p]'s tightened side in place.
            lower_sum = lower_without_me + min_contrib(cv, bounds[p]);
        }

        if (! equality || (! first && inference.count_inferences() == inferences_before_forward))
            break;

        auto inferences_before_inverse = inference.count_inferences();

        // Backward (>=): mirror of the forward pass on the inverse sum.
        Integer inv_lower_sum = -st.fixed_lower;
        for (std::size_t k = 0; k != st.n_active; ++k)
            inv_lower_sum += inv_contrib(coeff_vars.terms[active[k]], bounds[active[k]]);

        for (std::size_t k = 0; k != st.n_active; ++k) {
            auto p = active[k];
            const auto & cv = coeff_vars.terms[p];
            Integer inv_lower_without_me = inv_lower_sum - inv_contrib(cv, bounds[p]);
            Integer inv_remainder = -value - inv_lower_without_me;
            if (! infer(inference, logger, bounds, coeff_vars, p, get_var(cv), inv_remainder, negate(get_coeff_or_bool(cv)), true, proof_line,
                    add_to_reason, hint))
                return PropagatorState::Enable;
            // infer() has refreshed bounds[p]'s tightened side in place.
            inv_lower_sum = inv_lower_without_me + inv_contrib(cv, bounds[p]);
        }

        if (inference.count_inferences() == inferences_before_inverse)
            break;
    }

    // Fold any newly-instantiated active terms out of the active set, but ALWAYS keep at
    // least one term active: with everything folded, a fully-fixed but violated
    // assignment would be left unchecked (the loops above wouldn't run). Keeping one
    // active means the standard loop still verifies the (in)equality at a leaf, and
    // contradicts via the ordinary per-variable justification. The permutation is
    // persistent (never restored on backtrack); only n_active and fixed_lower are
    // backtracked, which is sound because the loops above are order-independent.
    for (std::size_t k = 0; k != st.n_active && st.n_active > 1;) {
        auto p = active[k];
        if (auto v = state.optional_single_value(get_var(coeff_vars.terms[p]))) {
            st.fixed_lower += get_coeff(coeff_vars.terms[p]) * *v;
            --st.n_active;
            std::swap(active[k], active[st.n_active]);
        }
        else
            ++k;
    }

    // Idempotent for both equality and inequality: the sweeps above ran to the
    // fixpoint, and the fold is internal bookkeeping, not inference -- it moves a
    // fixed term's contribution from the active sum into fixed_lower without
    // changing the total, so an immediate re-run computes the same remainders
    // (over the smaller active set plus the larger fixed_lower) and every guard
    // stays false.
    return PropagatorState::EnableButIdempotent;
}

// One instantiation per (coeff vector, tracker, hint): hints::LinearEquality for the
// equality MustHold path, NoHint for the inequality must-hold path.
#define GCS_INSTANTIATE_PROPAGATE_LINEAR_INCREMENTAL(CoeffVars, Tracker, Hint)                                                                       \
    template auto gcs::innards::propagate_linear_incremental(const CoeffVars & coeff_vars, Integer value, const State & state, Tracker &,            \
        ProofLogger * const logger, bool equality, const optional<pair<optional<ProofLine>, optional<ProofLine>>> & proof_line,                      \
        const optional<Literal> & add_to_reason, std::vector<std::size_t> & active, ConstraintStateHandle state_handle, const Hint & hint)           \
        -> PropagatorState

GCS_INSTANTIATE_PROPAGATE_LINEAR_INCREMENTAL(SumOf<Weighted<SimpleIntegerVariableID>>, SimpleInferenceTracker, hints::LinearEquality);
GCS_INSTANTIATE_PROPAGATE_LINEAR_INCREMENTAL(SumOf<PositiveOrNegative<SimpleIntegerVariableID>>, SimpleInferenceTracker, hints::LinearEquality);
GCS_INSTANTIATE_PROPAGATE_LINEAR_INCREMENTAL(SumOf<SimpleIntegerVariableID>, SimpleInferenceTracker, hints::LinearEquality);
GCS_INSTANTIATE_PROPAGATE_LINEAR_INCREMENTAL(SumOf<Weighted<SimpleIntegerVariableID>>, EagerProofLoggingInferenceTracker, hints::LinearEquality);
GCS_INSTANTIATE_PROPAGATE_LINEAR_INCREMENTAL(
    SumOf<PositiveOrNegative<SimpleIntegerVariableID>>, EagerProofLoggingInferenceTracker, hints::LinearEquality);
GCS_INSTANTIATE_PROPAGATE_LINEAR_INCREMENTAL(SumOf<SimpleIntegerVariableID>, EagerProofLoggingInferenceTracker, hints::LinearEquality);

GCS_INSTANTIATE_PROPAGATE_LINEAR_INCREMENTAL(SumOf<Weighted<SimpleIntegerVariableID>>, SimpleInferenceTracker, NoHint);
GCS_INSTANTIATE_PROPAGATE_LINEAR_INCREMENTAL(SumOf<PositiveOrNegative<SimpleIntegerVariableID>>, SimpleInferenceTracker, NoHint);
GCS_INSTANTIATE_PROPAGATE_LINEAR_INCREMENTAL(SumOf<SimpleIntegerVariableID>, SimpleInferenceTracker, NoHint);
GCS_INSTANTIATE_PROPAGATE_LINEAR_INCREMENTAL(SumOf<Weighted<SimpleIntegerVariableID>>, EagerProofLoggingInferenceTracker, NoHint);
GCS_INSTANTIATE_PROPAGATE_LINEAR_INCREMENTAL(SumOf<PositiveOrNegative<SimpleIntegerVariableID>>, EagerProofLoggingInferenceTracker, NoHint);
GCS_INSTANTIATE_PROPAGATE_LINEAR_INCREMENTAL(SumOf<SimpleIntegerVariableID>, EagerProofLoggingInferenceTracker, NoHint);

#undef GCS_INSTANTIATE_PROPAGATE_LINEAR_INCREMENTAL

template <typename Hint_>
auto gcs::innards::propagate_linear_not_equals(const auto & coeff_vars, Integer value, const State & state, auto & inference,
    ProofLogger * const logger, const vector<IntegerVariableID> & all_vars_for_reason, const Hint_ & hint) -> PropagatorState
{
    // condition is definitely false, so this is inequality. so long as at least two variables aren't
    // fixed, don't try to do anything.
    auto single_unset = coeff_vars.terms.end();
    Integer accum = 0_i;
    for (auto i = coeff_vars.terms.begin(), i_end = coeff_vars.terms.end(); i != i_end; ++i) {
        auto val = state.optional_single_value(get_var(*i));
        if (val)
            accum += get_coeff(*i) * *val;
        else {
            if (single_unset != coeff_vars.terms.end()) {
                // we've found at least two unset variables, do nothing for now
                return PropagatorState::Enable;
            }
            else
                single_unset = i;
        }
    }

    if (single_unset == coeff_vars.terms.end()) {
        // every variable is set, do a sanity check
        if (accum == value) {
            // we've set every variable and have equality
            inference.contradiction(logger, JustifyUsingRUP{hint}, generic_reason(all_vars_for_reason));
        }
        else
            return PropagatorState::DisableUntilBacktrack;
    }
    else {
        // exactly one thing remaining, so it can't be given the single value that would
        // make the equality hold.
        Integer residual = value - accum;
        if (0_i == residual % get_coeff(*single_unset)) {
            Integer forbidden = residual / get_coeff(*single_unset);
            if (state.in_domain(get_var(*single_unset), forbidden)) {
                // the forbidden value is in the domain, so disallow it, and then
                // we won't do anything else.
                inference.infer(logger, get_var(*single_unset) != forbidden, JustifyUsingRUP{hint}, generic_reason(all_vars_for_reason));
                return PropagatorState::DisableUntilBacktrack;
            }
            else {
                // the forbidden value isn't in the domain, we're not going to do
                // anything else
                return PropagatorState::DisableUntilBacktrack;
            }
        }
        else {
            // the forbidden value isn't an integer, so it can't happen
            return PropagatorState::DisableUntilBacktrack;
        }
    }
}

// As with propagate_linear: one instantiation per (coeff vector, tracker, hint)
// pair. hints::LinearNotEquals for the LinearNotEquals / LinearNotEqualsIf
// propagators; NoHint kept for the defaulted hint so a future non-hinting caller
// still links.
#define GCS_INSTANTIATE_PROPAGATE_LINEAR_NOT_EQUALS(CoeffVars, Tracker, Hint)                                                                        \
    template auto gcs::innards::propagate_linear_not_equals(const CoeffVars & terms, Integer, const State &, Tracker &, ProofLogger * const logger,  \
        const vector<IntegerVariableID> & all_vars_for_reason, const Hint & hint) -> PropagatorState

GCS_INSTANTIATE_PROPAGATE_LINEAR_NOT_EQUALS(SumOf<Weighted<SimpleIntegerVariableID>>, SimpleInferenceTracker, hints::LinearNotEquals);
GCS_INSTANTIATE_PROPAGATE_LINEAR_NOT_EQUALS(SumOf<PositiveOrNegative<SimpleIntegerVariableID>>, SimpleInferenceTracker, hints::LinearNotEquals);
GCS_INSTANTIATE_PROPAGATE_LINEAR_NOT_EQUALS(SumOf<SimpleIntegerVariableID>, SimpleInferenceTracker, hints::LinearNotEquals);
GCS_INSTANTIATE_PROPAGATE_LINEAR_NOT_EQUALS(SumOf<Weighted<SimpleIntegerVariableID>>, EagerProofLoggingInferenceTracker, hints::LinearNotEquals);
GCS_INSTANTIATE_PROPAGATE_LINEAR_NOT_EQUALS(
    SumOf<PositiveOrNegative<SimpleIntegerVariableID>>, EagerProofLoggingInferenceTracker, hints::LinearNotEquals);
GCS_INSTANTIATE_PROPAGATE_LINEAR_NOT_EQUALS(SumOf<SimpleIntegerVariableID>, EagerProofLoggingInferenceTracker, hints::LinearNotEquals);

GCS_INSTANTIATE_PROPAGATE_LINEAR_NOT_EQUALS(SumOf<Weighted<SimpleIntegerVariableID>>, SimpleInferenceTracker, NoHint);
GCS_INSTANTIATE_PROPAGATE_LINEAR_NOT_EQUALS(SumOf<PositiveOrNegative<SimpleIntegerVariableID>>, SimpleInferenceTracker, NoHint);
GCS_INSTANTIATE_PROPAGATE_LINEAR_NOT_EQUALS(SumOf<SimpleIntegerVariableID>, SimpleInferenceTracker, NoHint);
GCS_INSTANTIATE_PROPAGATE_LINEAR_NOT_EQUALS(SumOf<Weighted<SimpleIntegerVariableID>>, EagerProofLoggingInferenceTracker, NoHint);
GCS_INSTANTIATE_PROPAGATE_LINEAR_NOT_EQUALS(SumOf<PositiveOrNegative<SimpleIntegerVariableID>>, EagerProofLoggingInferenceTracker, NoHint);
GCS_INSTANTIATE_PROPAGATE_LINEAR_NOT_EQUALS(SumOf<SimpleIntegerVariableID>, EagerProofLoggingInferenceTracker, NoHint);

#undef GCS_INSTANTIATE_PROPAGATE_LINEAR_NOT_EQUALS
