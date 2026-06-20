#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_INFERENCE_TRACKER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_INFERENCE_TRACKER_HH

#include <gcs/innards/assertion_hints.hh>
#include <gcs/innards/inference_tracker-fwd.hh>
#include <gcs/innards/justification.hh>
#include <gcs/innards/proofs/infer_witness.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/state.hh>

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
            if (! logger)
                return NoReason{};

            return reason.visit(overloaded{
                [&](const NoReason &) -> Reason { return NoReason{}; },
                [&](const LazyReasonOver &) -> Reason { return reason; },
                [&](const NarrowableLazyReasonOver &) -> Reason { return reason; },
                [&](const auto &) -> Reason { return ExplicitReason{materialise(reason, state)}; }});
        }

        // The bookkeeping for a firing (non-NoChange, non-Contradiction) inference:
        // record the affected variable for later replay and mark that propagation
        // did something. Shared by the witness path (track_witness) and the variant
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

        // The witness counterpart of track_impl. Lives in the base class because it
        // needs no per-tracker behaviour: the witness is consumed (built into proof
        // steps or an assertion) only when there is a logger, so the Simple,
        // proofs-off tracker never touches it (pay-for-use) and the same body serves
        // both trackers. Dispatch onto the witness is compile-time overload
        // resolution inside infer_witness; no std::function is involved.
        template <typename Witness_>
        auto track_witness(ProofLogger * const logger, const Inference inf, const Literal & lit,
            const JustifyByWitness<Witness_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback) -> void
        {
            switch (inf) {
            case Inference::NoChange:
                break;

            case Inference::InteriorValuesChanged:
            case Inference::BoundsChanged:
            case Inference::Instantiated:
                if (logger)
                    infer_witness(*logger, lit, why.witness, why.then_rup, materialise(reason, _state), fallback);
                record_firing_inference(inf, lit);
                break;

            [[unlikely]] case Inference::Contradiction:
                if (logger)
                    infer_witness(*logger, lit, why.witness, why.then_rup, materialise(reason, _state), fallback);
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

        // Justify an inference with a typed witness (JustifyByWitness): the
        // pay-for-use, std::function-free path. The fallback annotation is used in
        // assertion mode only when the witness carries no hint of its own, matching
        // JustifyByData's empty-annotation behaviour.
        template <typename Witness_>
        auto infer(ProofLogger * const logger, const Literal & lit, const JustifyByWitness<Witness_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            auto snapshotted = snapshot_reason(logger, reason, _state);
            track_witness(logger, _state.infer(lit), lit, why, snapshotted, fallback);
        }

        [[noreturn]] auto contradiction(ProofLogger * const logger, const Justification & why, const Reason & reason, const std::optional<AssertionAnnotation> & assertion_hints = std::nullopt) -> void
        {
            // No domain change happens here, so the reason materialises against
            // the current state directly (the eager/lazy timing distinction only
            // matters when there is an inference to straddle).
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
            // For an explicit-steps-then-RUP justification (JustifyByData with an
            // emit and then_rup): enter the temporary proof level once, run the
            // explicit scaffolding once, then RUP each inference under the shared
            // scaffolding. Without this, each infer() would enter and exit its own
            // temporary level, wiping the scaffolding before subsequent inferences
            // can use it.
            if (logger && logger->get_assertion_level() == AssertionLevel::Off &&
                std::holds_alternative<JustifyByData>(why) && std::get<JustifyByData>(why).emit && std::get<JustifyByData>(why).then_rup) {
                // The scaffolding is shared across the batch, but each inference's
                // RUP is only emitted if it actually changes something (track_impl
                // drops NoChange). If *every* inference is already entailed, no RUP
                // would reference the scaffolding, so emitting it is wasted work
                // (and leaves an unreferenced constraint for forget to delete).
                // Only emit when at least one inference will fire. (A single infer()
                // is already lazy this way: track_impl gates logger->infer on the
                // inference changing something.)
                auto any_will_fire = false;
                for (const auto & lit : lits)
                    if (_state.test_literal(lit) != LiteralIs::DefinitelyTrue) {
                        any_will_fire = true;
                        break;
                    }
                if (! any_will_fire)
                    return;

                // Snapshot the shared reason once, pre-batch (matching the old
                // single eager build): eager reasons become a fixed ExplicitReason
                // reused for the scaffolding and every RUP; lazy reasons stay
                // declarative and re-materialise per inference inside the loop.
                auto snapshotted = snapshot_reason(logger, reason, _state);
                ReasonLiterals reason_lits = materialise(snapshotted, _state);
                const auto & j = std::get<JustifyByData>(why);
                auto t = logger->temporary_proof_level();
                j.emit(reason_lits);
                for (const auto & lit : lits)
                    infer(logger, lit, JustifyUsingRUP{}, snapshotted);
                logger->forget_proof_level(t);
            }
            else {
                auto snapshotted = snapshot_reason(logger, reason, _state);
                for (const auto & lit : lits)
                    infer(logger, lit, why, snapshotted, assertion_hints);
            }
        }

        // The witness counterpart of infer_all: same shared-temporary-level batching
        // for the explicit-steps-then-RUP shape, but the scaffolding is emitted by
        // the witness's emit_justification rather than a JustifyByData::emit closure.
        template <typename Witness_>
        auto infer_all(ProofLogger * const logger, const std::vector<Literal> & lits, const JustifyByWitness<Witness_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            if (logger && logger->get_assertion_level() == AssertionLevel::Off && why.then_rup) {
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
                emit_justification(*logger, why.witness, reason_lits);
                for (const auto & lit : lits)
                    infer(logger, lit, JustifyUsingRUP{}, snapshotted);
                logger->forget_proof_level(t);
            }
            else {
                auto snapshotted = snapshot_reason(logger, reason, _state);
                for (const auto & lit : lits)
                    infer(logger, lit, why, snapshotted, fallback);
            }
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
