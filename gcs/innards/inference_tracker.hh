#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_INFERENCE_TRACKER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_INFERENCE_TRACKER_HH

#include <gcs/innards/assertion_hints.hh>
#include <gcs/innards/inference_tracker-fwd.hh>
#include <gcs/innards/justification.hh>
#include <gcs/innards/proofs/infer_explicitly.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/state.hh>

#include <concepts>
#include <deque>
#include <optional>
#include <utility>
#include <version>

#include <util/overloaded.hh>

#ifdef __cpp_lib_generator
#include <generator>
#else
#include <__generator.hpp>
#endif

namespace gcs::innards
{
    class TrackedPropagationFailed
    {
    };

    template <typename Actual_>
    class InferenceTrackerBase
    {
    protected:
        State & _state;
        std::deque<std::pair<SimpleIntegerVariableID, Inference>> _inferences;
        bool _did_anything_since_last_call_by_propagation_queue, _did_anything_since_last_call_inside_propagator;

        auto track(ProofLogger * const logger, const Inference inf, const Literal & lit, const Justification & just, const Reason & reason, const std::optional<AssertionAnnotation> & assertion_hints = std::nullopt) -> void
        {
            return static_cast<Actual_ *>(this)->track_impl(logger, inf, lit, just, reason, assertion_hints);
        }

        // Pin a reason's materialisation *timing* so it can be carried across the
        // domain change in track() and materialised by the logger-side tracker
        // afterwards, while staying byte-identical to the old eager call sites:
        //   - proofs off (logger == nullptr): never materialise. The reason is
        //     ignored by the simple tracker, so building its literals would be
        //     the wasted eager-build-then-discard this rework removes (G1).
        //   - the *_reason() factories (Generic / BothBounds / Explicit): these
        //     used to be built eagerly at the call site, against the pre-inference
        //     state. Snapshot them now, before _state.infer(), into an
        //     ExplicitReason that later re-materialises to the same literals
        //     regardless of state.
        //   - the Lazy variants: these used to be evaluated by the logger, after
        //     the inference. Carry the declarative reason unchanged so it
        //     materialises against the (post-inference) state later.
        [[nodiscard]] static auto snapshot_reason(ProofLogger * const logger, const Reason & reason, State & state) -> Reason
        {
            // The proofs-off (non-materialising) tracker never reads the reason, so
            // this collapses to a constant NoReason there and the whole call — and
            // the snapshotted Reason it would have produced — is dead-code eliminated.
            if constexpr (! Actual_::materialises_reasons)
                return NoReason{};
            else {
                if (! logger)
                    return NoReason{};

                return reason.visit(overloaded{
                    [&](const NoReason &) -> Reason { return NoReason{}; },
                    [&](const LazyReasonOver &) -> Reason { return reason; },
                    [&](const NarrowableLazyReasonOver &) -> Reason { return reason; },
                    [&](const auto &) -> Reason { return ExplicitReason{materialise(reason, state)}; }});
            }
        }

        // The bookkeeping for a firing (non-NoChange, non-Contradiction) inference:
        // record the affected variable for later replay and mark that propagation
        // did something. Shared by the explicit path (track_explicit) and the variant
        // track_impl bodies below.
        auto record_firing_inference(const Inference inf, const Literal & lit) -> void
        {
            overloaded{
                [&](const TrueLiteral &) {},
                [&](const FalseLiteral &) {},
                [&](const IntegerVariableCondition & cond) {
                    overloaded{
                        [&](const ConstantIntegerVariableID &) {},
                        [&](const SimpleIntegerVariableID & var) {
                            _inferences.emplace_back(var, inf);
                        },
                        [&](const ViewOfIntegerVariableID & var) {
                            _inferences.emplace_back(var.actual_variable, inf);
                        }}
                        .visit(cond.var);
                }}
                .visit(lit);

            _did_anything_since_last_call_by_propagation_queue = true;
            _did_anything_since_last_call_inside_propagator = true;
        }

        // The JustifyExplicitly counterpart of track_impl. Lives in the base class
        // because it needs no per-tracker behaviour: the emit/hint are consumed (built
        // into proof steps or an assertion) only when there is a logger, so the
        // Simple, proofs-off tracker never touches them (pay-for-use) and the same
        // body serves both trackers. Dispatch is compile-time overload resolution
        // inside infer_explicitly; no std::function is involved.
        template <typename Emit_, typename Hint_>
        auto track_explicit(ProofLogger * const logger, const Inference inf, const Literal & lit,
            const JustifyExplicitly<Emit_, Hint_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback) -> void
        {
            switch (inf) {
            case Inference::NoChange:
                break;

            case Inference::InteriorValuesChanged:
            case Inference::BoundsChanged:
            case Inference::Instantiated:
                if constexpr (Actual_::materialises_reasons)
                    if (logger)
                        infer_explicitly(*logger, lit, why.emit, why.then_rup, materialise(reason, _state), why.hint, fallback);
                record_firing_inference(inf, lit);
                break;

            [[unlikely]] case Inference::Contradiction:
                if constexpr (Actual_::materialises_reasons)
                    if (logger)
                        infer_explicitly(*logger, lit, why.emit, why.then_rup, materialise(reason, _state), why.hint, fallback);
                _did_anything_since_last_call_by_propagation_queue = true;
                _did_anything_since_last_call_inside_propagator = true;
                throw TrackedPropagationFailed{};
            }
        }

    public:
        explicit InferenceTrackerBase(State & s) :
            _state(s),
            _did_anything_since_last_call_by_propagation_queue(false),
            _did_anything_since_last_call_inside_propagator(false)
        {
        }

        InferenceTrackerBase(const InferenceTrackerBase &) = delete;

        auto operator=(const InferenceTrackerBase &) -> InferenceTrackerBase & = delete;

        auto infer(ProofLogger * const logger, const Literal & lit, const Justification & why, const Reason & reason, const std::optional<AssertionAnnotation> & assertion_hints = std::nullopt) -> void
        {
            auto snapshotted = snapshot_reason(logger, reason, _state);
            track(logger, _state.infer(lit), lit, why, snapshotted, assertion_hints);
        }

        // Justify an inference with explicit proof steps (JustifyExplicitly): the
        // pay-for-use, std::function-free explicit-steps path. The fallback
        // annotation is used in assertion mode only when the justification carries no
        // hint of its own. There is an overload for each plain infer entry point
        // (general literal, the typed condition/bound helpers, and contradiction);
        // each just routes to track_explicit instead of track.
        template <typename Emit_, typename Hint_>
        auto infer(ProofLogger * const logger, const Literal & lit, const JustifyExplicitly<Emit_, Hint_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            auto snapshotted = snapshot_reason(logger, reason, _state);
            track_explicit(logger, _state.infer(lit), lit, why, snapshotted, fallback);
        }

        // Visit a variant of justifications and dispatch each alternative to its
        // matching infer overload. This is how the reified dispatcher's verdict —
        // which carries a per-constraint variant of justification shapes (plain
        // Justification alternatives and/or typed JustifyExplicitly) — is applied:
        // the dispatcher just forwards the verdict's justification here, so the
        // visit lives in infer() rather than at the call site. (The non-template
        // const Justification & overload is preferred for a Justification argument,
        // so the variant overload only catches the per-constraint variants.)
        template <typename... Alts_>
        auto infer(ProofLogger * const logger, const Literal & lit, const std::variant<Alts_...> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            std::visit([&](const auto & alt) { infer(logger, lit, alt, reason, fallback); }, why);
        }

        template <IntegerVariableIDLike VarType_, typename Emit_, typename Hint_>
        auto infer(ProofLogger * const logger, const VariableConditionFrom<VarType_> & lit, const JustifyExplicitly<Emit_, Hint_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            auto snapshotted = snapshot_reason(logger, reason, _state);
            track_explicit(logger, _state.infer(lit), lit, why, snapshotted, fallback);
        }

        template <typename Emit_, typename Hint_>
        [[noreturn]] auto contradiction(ProofLogger * const logger, const JustifyExplicitly<Emit_, Hint_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            if constexpr (Actual_::materialises_reasons)
                if (logger)
                    infer_explicitly(*logger, FalseLiteral{}, why.emit, why.then_rup, materialise(reason, _state), why.hint, fallback);
            throw TrackedPropagationFailed{};
        }

        template <IntegerVariableIDLike VarType_, typename Emit_, typename Hint_>
        auto infer_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const JustifyExplicitly<Emit_, Hint_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            auto snapshotted = snapshot_reason(logger, reason, _state);
            track_explicit(logger, _state.infer_equal(var, value), var == value, why, snapshotted, fallback);
        }

        template <IntegerVariableIDLike VarType_, typename Emit_, typename Hint_>
        auto infer_not_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const JustifyExplicitly<Emit_, Hint_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            auto snapshotted = snapshot_reason(logger, reason, _state);
            track_explicit(logger, _state.infer_not_equal(var, value), var != value, why, snapshotted, fallback);
        }

        // A JustifyUsingRUP carrying a typed hint is a RUP inference (no explicit
        // steps) that wants a typed assertion hint. Each overload below turns the
        // hint into an annotation (only when something will be asserted — Off mode
        // builds nothing, so it stays byte-identical to a bare RUP) and delegates to
        // the plain JustifyUsingRUP{} path. No explicit-steps machinery is involved.
        template <typename Hint_>
        [[nodiscard]] auto rup_hint_annotation(ProofLogger * const logger, const Hint_ & hint, const std::optional<AssertionAnnotation> & fallback) -> std::optional<AssertionAnnotation>
        {
            if (logger && logger->get_assertion_level() != AssertionLevel::Off)
                return hint_annotation(*logger, hint, fallback);
            return fallback;
        }

        template <typename Hint_>
            requires(! std::same_as<Hint_, NoHint>)
        auto infer(ProofLogger * const logger, const Literal & lit, const JustifyUsingRUP<Hint_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            infer(logger, lit, JustifyUsingRUP{}, reason, rup_hint_annotation(logger, why.hint, fallback));
        }

        template <IntegerVariableIDLike VarType_, typename Hint_>
            requires(! std::same_as<Hint_, NoHint>)
        auto infer_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const JustifyUsingRUP<Hint_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            infer_equal(logger, var, value, JustifyUsingRUP{}, reason, rup_hint_annotation(logger, why.hint, fallback));
        }

        template <IntegerVariableIDLike VarType_, typename Hint_>
            requires(! std::same_as<Hint_, NoHint>)
        auto infer_not_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const JustifyUsingRUP<Hint_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            infer_not_equal(logger, var, value, JustifyUsingRUP{}, reason, rup_hint_annotation(logger, why.hint, fallback));
        }

        template <IntegerVariableIDLike VarType_, typename Hint_>
            requires(! std::same_as<Hint_, NoHint>)
        auto infer_less_than(ProofLogger * const logger, const VarType_ & var, Integer value, const JustifyUsingRUP<Hint_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            infer_less_than(logger, var, value, JustifyUsingRUP{}, reason, rup_hint_annotation(logger, why.hint, fallback));
        }

        template <IntegerVariableIDLike VarType_, typename Hint_>
            requires(! std::same_as<Hint_, NoHint>)
        auto infer_greater_than_or_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const JustifyUsingRUP<Hint_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            infer_greater_than_or_equal(logger, var, value, JustifyUsingRUP{}, reason, rup_hint_annotation(logger, why.hint, fallback));
        }

        template <typename Hint_>
            requires(! std::same_as<Hint_, NoHint>)
        auto infer_all(ProofLogger * const logger, const std::vector<Literal> & lits, const JustifyUsingRUP<Hint_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            infer_all(logger, lits, JustifyUsingRUP{}, reason, rup_hint_annotation(logger, why.hint, fallback));
        }

        template <typename Hint_>
            requires(! std::same_as<Hint_, NoHint>)
        [[noreturn]] auto contradiction(ProofLogger * const logger, const JustifyUsingRUP<Hint_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            contradiction(logger, JustifyUsingRUP{}, reason, rup_hint_annotation(logger, why.hint, fallback));
        }

        template <IntegerVariableIDLike VarType_, typename Hint_>
            requires(! std::same_as<Hint_, NoHint>)
        auto infer_not_in_range(ProofLogger * const logger, const VarType_ & var, Integer lo, Integer hi, const JustifyUsingRUP<Hint_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            infer_not_in_range(logger, var, lo, hi, JustifyUsingRUP{}, reason, rup_hint_annotation(logger, why.hint, fallback));
        }

        template <IntegerVariableIDLike VarType_, typename Emit_, typename Hint_>
        auto infer_less_than(ProofLogger * const logger, const VarType_ & var, Integer value, const JustifyExplicitly<Emit_, Hint_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            auto snapshotted = snapshot_reason(logger, reason, _state);
            track_explicit(logger, _state.infer_less_than(var, value), var < value, why, snapshotted, fallback);
        }

        template <IntegerVariableIDLike VarType_, typename Emit_, typename Hint_>
        auto infer_greater_than_or_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const JustifyExplicitly<Emit_, Hint_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            auto snapshotted = snapshot_reason(logger, reason, _state);
            track_explicit(logger, _state.infer_greater_than_or_equal(var, value), var >= value, why, snapshotted, fallback);
        }

        template <IntegerVariableIDLike VarType_, typename Emit_, typename Hint_>
        auto infer_not_in_range(ProofLogger * const logger, const VarType_ & var, Integer lo, Integer hi, const JustifyExplicitly<Emit_, Hint_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            if (lo > hi)
                return;
            auto snapshotted = snapshot_reason(logger, reason, _state);
            track_explicit(logger, _state.infer_not_in_range(var, lo, hi), not_in_range(var, lo, hi), why, snapshotted, fallback);
        }

        [[noreturn]] auto contradiction(ProofLogger * const logger, const Justification & why, const Reason & reason, const std::optional<AssertionAnnotation> & assertion_hints = std::nullopt) -> void
        {
            // No domain change happens here, so the reason materialises against
            // the current state directly (the eager/lazy timing distinction only
            // matters when there is an inference to straddle).
            if constexpr (Actual_::materialises_reasons)
                if (logger)
                    logger->infer(FalseLiteral{}, why, materialise(reason, _state), assertion_hints);
            throw TrackedPropagationFailed{};
        }

        template <IntegerVariableIDLike VarType_>
        auto infer(ProofLogger * const logger, const VariableConditionFrom<VarType_> & lit, const Justification & why, const Reason & reason, const std::optional<AssertionAnnotation> & assertion_hints = std::nullopt) -> void
        {
            auto snapshotted = snapshot_reason(logger, reason, _state);
            track(logger, _state.infer(lit), lit, why, snapshotted, assertion_hints);
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const Reason & reason, const std::optional<AssertionAnnotation> & assertion_hints = std::nullopt) -> void
        {
            auto snapshotted = snapshot_reason(logger, reason, _state);
            track(logger, _state.infer_equal(var, value), var == value, why, snapshotted, assertion_hints);
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_not_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const Reason & reason, const std::optional<AssertionAnnotation> & assertion_hints = std::nullopt) -> void
        {
            auto snapshotted = snapshot_reason(logger, reason, _state);
            track(logger, _state.infer_not_equal(var, value), var != value, why, snapshotted, assertion_hints);
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_less_than(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const Reason & reason, const std::optional<AssertionAnnotation> & assertion_hints = std::nullopt) -> void
        {
            auto snapshotted = snapshot_reason(logger, reason, _state);
            track(logger, _state.infer_less_than(var, value), var < value, why, snapshotted, assertion_hints);
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_greater_than_or_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const Reason & reason, const std::optional<AssertionAnnotation> & assertion_hints = std::nullopt) -> void
        {
            auto snapshotted = snapshot_reason(logger, reason, _state);
            track(logger, _state.infer_greater_than_or_equal(var, value), var >= value, why, snapshotted, assertion_hints);
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_not_in_range(ProofLogger * const logger, const VarType_ & var, Integer lo, Integer hi, const Justification & why, const Reason & reason, const std::optional<AssertionAnnotation> & assertion_hints = std::nullopt) -> void
        {
            // The conclusion is the ordinary range condition; the state update
            // batches the whole removal into one erase_range pass.
            if (lo > hi)
                return;
            auto snapshotted = snapshot_reason(logger, reason, _state);
            track(logger, _state.infer_not_in_range(var, lo, hi), not_in_range(var, lo, hi), why, snapshotted, assertion_hints);
        }

        auto infer_all(ProofLogger * const logger, const std::vector<Literal> & lits, const Justification & why, const Reason & reason, const std::optional<AssertionAnnotation> & assertion_hints = std::nullopt) -> void
        {
            // The plain justifications (RUP / assert / none) carry no shared
            // scaffolding to batch, so infer each literal in turn. The
            // explicit-steps batching (enter one temporary level, emit the
            // scaffolding once, RUP each inference under it) lives on the
            // JustifyExplicitly infer_all overload below.
            auto snapshotted = snapshot_reason(logger, reason, _state);
            for (const auto & lit : lits)
                infer(logger, lit, why, snapshotted, assertion_hints);
        }

        // The JustifyExplicitly counterpart of infer_all. When the steps end in a
        // RUP (ThenRUP::Yes) and proofs are Off, it does the shared-temporary-level
        // batching: emit the scaffolding once via the emit callable, then RUP each
        // inference under it. Otherwise (assertion mode, or ThenRUP::No) it falls
        // through to the per-literal path, where each inference carries the
        // assertion hint in assert mode.
        template <typename Emit_, typename Hint_>
        auto infer_all(ProofLogger * const logger, const std::vector<Literal> & lits, const JustifyExplicitly<Emit_, Hint_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            if constexpr (Actual_::materialises_reasons) {
                if (logger && logger->get_assertion_level() == AssertionLevel::Off && why.then_rup == ThenRUP::Yes) {
                    auto any_will_fire = false;
                    for (const auto & lit : lits)
                        if (_state.test_literal(lit) != LiteralIs::DefinitelyTrue) {
                            any_will_fire = true;
                            break;
                        }
                    if (! any_will_fire)
                        return;

                    auto snapshotted = snapshot_reason(logger, reason, _state);
                    ReasonLiterals reason_lits = materialise(snapshotted, _state);
                    auto t = logger->temporary_proof_level();
                    emit_explicit_steps(*logger, why.emit, reason_lits);
                    for (const auto & lit : lits)
                        infer(logger, lit, JustifyUsingRUP{}, snapshotted);
                    logger->forget_proof_level(t);
                    return;
                }
            }

            auto snapshotted = snapshot_reason(logger, reason, _state);
            for (const auto & lit : lits)
                infer(logger, lit, why, snapshotted, fallback);
        }

        auto each_inference() const -> std::generator<std::pair<SimpleIntegerVariableID, Inference>>
        {
            return [](const auto & inferences) -> std::generator<std::pair<SimpleIntegerVariableID, Inference>> {
                for (const auto & [var, inf] : inferences | std::ranges::views::reverse)
                    co_yield std::pair{var, inf};
            }(_inferences);
        }

        auto reset() -> void
        {
            _inferences.clear();
            _did_anything_since_last_call_inside_propagator = false;
            _did_anything_since_last_call_by_propagation_queue = false;
        }

        auto did_anything_since_last_call_by_propagation_queue() -> bool
        {
            return std::exchange(_did_anything_since_last_call_by_propagation_queue, false);
        }

        auto did_anything_since_last_call_inside_propagator() -> bool
        {
            return std::exchange(_did_anything_since_last_call_inside_propagator, false);
        }
    };

    class SimpleInferenceTracker : public InferenceTrackerBase<SimpleInferenceTracker>
    {
    public:
        using InferenceTrackerBase::InferenceTrackerBase;

        // Proofs-off tracker: it never materialises a reason, so the base infer()
        // path skips snapshot_reason and every proof-only block compiles out.
        static constexpr bool materialises_reasons = false;

        auto track_impl(ProofLogger * const, const Inference inf, const Literal & lit, const Justification &, const Reason &, const std::optional<AssertionAnnotation> &) -> void
        {
            switch (inf) {
            case Inference::NoChange:
                break;

            case Inference::InteriorValuesChanged:
            case Inference::BoundsChanged:
            case Inference::Instantiated:
                overloaded{
                    [&](const TrueLiteral &) {},
                    [&](const FalseLiteral &) {},
                    [&](const IntegerVariableCondition & cond) {
                        overloaded{
                            [&](const ConstantIntegerVariableID &) {},
                            [&](const SimpleIntegerVariableID & var) {
                                _inferences.emplace_back(var, inf);
                            },
                            [&](const ViewOfIntegerVariableID & var) {
                                _inferences.emplace_back(var.actual_variable, inf);
                            }}
                            .visit(cond.var);
                    }}
                    .visit(lit);

                _did_anything_since_last_call_by_propagation_queue = true;
                _did_anything_since_last_call_inside_propagator = true;
                break;

            [[unlikely]] case Inference::Contradiction:
                _did_anything_since_last_call_by_propagation_queue = true;
                _did_anything_since_last_call_inside_propagator = true;
                throw TrackedPropagationFailed{};
            }
        }
    };

    class EagerProofLoggingInferenceTracker : public InferenceTrackerBase<EagerProofLoggingInferenceTracker>
    {
    public:
        using InferenceTrackerBase::InferenceTrackerBase;

        static constexpr bool materialises_reasons = true;

        auto track_impl(ProofLogger * const logger, const Inference inf, const Literal & lit, const Justification & just, const Reason & reason, const std::optional<AssertionAnnotation> & assertion_hints = std::nullopt) -> void
        {
            switch (inf) {
            case Inference::NoChange:
                break;

            case Inference::InteriorValuesChanged:
            case Inference::BoundsChanged:
            case Inference::Instantiated:
                if (logger) {
                    // Materialise the reason here, post-inference: snapshot_reason
                    // already pinned the timing (eager kinds are a fixed
                    // ExplicitReason snapshot taken pre-inference, Lazy kinds stay
                    // declarative and materialise against the now-current state),
                    // so materialising now gives both kinds the literals the logger
                    // used to compute internally.
                    logger->infer(lit, just, materialise(reason, _state), assertion_hints);
                }

                overloaded{
                    [&](const TrueLiteral &) {},
                    [&](const FalseLiteral &) {},
                    [&](const IntegerVariableCondition & cond) {
                        overloaded{
                            [&](const ConstantIntegerVariableID &) {},
                            [&](const SimpleIntegerVariableID & var) {
                                _inferences.emplace_back(var, inf);
                            },
                            [&](const ViewOfIntegerVariableID & var) {
                                _inferences.emplace_back(var.actual_variable, inf);
                            }}
                            .visit(cond.var);
                    }}
                    .visit(lit);

                _did_anything_since_last_call_by_propagation_queue = true;
                _did_anything_since_last_call_inside_propagator = true;
                break;

            [[unlikely]] case Inference::Contradiction:
                if (logger)
                    logger->infer(lit, just, materialise(reason, _state), assertion_hints);
                _did_anything_since_last_call_by_propagation_queue = true;
                _did_anything_since_last_call_inside_propagator = true;
                throw TrackedPropagationFailed{};
            }
        }
    };
}

#endif
