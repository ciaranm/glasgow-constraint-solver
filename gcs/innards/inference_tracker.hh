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
        // pay-for-use, std::function-free explicit-steps path. The fallback
        // annotation is used in assertion mode only when the witness carries no hint
        // of its own. There is a witness overload for each plain infer entry point
        // (general literal, the typed condition/bound helpers, and contradiction);
        // each just routes to track_witness instead of track.
        template <typename Witness_>
        auto infer(ProofLogger * const logger, const Literal & lit, const JustifyByWitness<Witness_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            auto snapshotted = snapshot_reason(logger, reason, _state);
            track_witness(logger, _state.infer(lit), lit, why, snapshotted, fallback);
        }

        // Visit a variant of justifications and dispatch each alternative to its
        // matching infer overload. This is how the reified dispatcher's verdict —
        // which carries a per-constraint variant of justification shapes (plain
        // Justification alternatives and/or typed JustifyByWitness) — is applied:
        // the dispatcher just forwards the verdict's justification here, so the
        // visit lives in infer() rather than at the call site. (The non-template
        // const Justification & overload is preferred for a Justification argument,
        // so the variant overload only catches the per-constraint variants.)
        template <typename... Alts_>
        auto infer(ProofLogger * const logger, const Literal & lit, const std::variant<Alts_...> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            std::visit([&](const auto & alt) { infer(logger, lit, alt, reason, fallback); }, why);
        }

        template <IntegerVariableIDLike VarType_, typename Witness_>
        auto infer(ProofLogger * const logger, const VariableConditionFrom<VarType_> & lit, const JustifyByWitness<Witness_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            auto snapshotted = snapshot_reason(logger, reason, _state);
            track_witness(logger, _state.infer(lit), lit, why, snapshotted, fallback);
        }

        template <typename Witness_>
        [[noreturn]] auto contradiction(ProofLogger * const logger, const JustifyByWitness<Witness_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            if (logger)
                infer_witness(*logger, FalseLiteral{}, why.witness, why.then_rup, materialise(reason, _state), fallback);
            throw TrackedPropagationFailed{};
        }

        template <IntegerVariableIDLike VarType_, typename Witness_>
        auto infer_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const JustifyByWitness<Witness_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            auto snapshotted = snapshot_reason(logger, reason, _state);
            track_witness(logger, _state.infer_equal(var, value), var == value, why, snapshotted, fallback);
        }

        template <IntegerVariableIDLike VarType_, typename Witness_>
        auto infer_not_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const JustifyByWitness<Witness_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            auto snapshotted = snapshot_reason(logger, reason, _state);
            track_witness(logger, _state.infer_not_equal(var, value), var != value, why, snapshotted, fallback);
        }

        template <IntegerVariableIDLike VarType_, typename Witness_>
        auto infer_less_than(ProofLogger * const logger, const VarType_ & var, Integer value, const JustifyByWitness<Witness_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            auto snapshotted = snapshot_reason(logger, reason, _state);
            track_witness(logger, _state.infer_less_than(var, value), var < value, why, snapshotted, fallback);
        }

        template <IntegerVariableIDLike VarType_, typename Witness_>
        auto infer_greater_than_or_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const JustifyByWitness<Witness_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            auto snapshotted = snapshot_reason(logger, reason, _state);
            track_witness(logger, _state.infer_greater_than_or_equal(var, value), var >= value, why, snapshotted, fallback);
        }

        template <IntegerVariableIDLike VarType_, typename Witness_>
        auto infer_not_in_range(ProofLogger * const logger, const VarType_ & var, Integer lo, Integer hi, const JustifyByWitness<Witness_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            if (lo > hi)
                return;
            auto snapshotted = snapshot_reason(logger, reason, _state);
            track_witness(logger, _state.infer_not_in_range(var, lo, hi), not_in_range(var, lo, hi), why, snapshotted, fallback);
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
            // The plain justifications (RUP / assert / none) carry no shared
            // scaffolding to batch, so infer each literal in turn. The
            // explicit-steps batching (enter one temporary level, emit the
            // scaffolding once, RUP each inference under it) lives on the
            // JustifyByWitness infer_all overload below.
            auto snapshotted = snapshot_reason(logger, reason, _state);
            for (const auto & lit : lits)
                infer(logger, lit, why, snapshotted, assertion_hints);
        }

        // The witness counterpart of infer_all. For an explicit-steps witness it
        // does the same shared-temporary-level batching as the variant infer_all,
        // emitting the scaffolding once via emit_justification then RUPing each
        // inference. A pure-RUP witness has no scaffolding to share, so it falls
        // through to the per-literal path (each inference RUPs under the reason,
        // carrying the witness's assertion hint in assert mode).
        template <typename Witness_>
        auto infer_all(ProofLogger * const logger, const std::vector<Literal> & lits, const JustifyByWitness<Witness_> & why, const Reason & reason, const std::optional<AssertionAnnotation> & fallback = std::nullopt) -> void
        {
            if constexpr (WitnessHasExplicitSteps<Witness_>) {
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
