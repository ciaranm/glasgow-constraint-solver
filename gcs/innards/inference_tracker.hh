#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_INFERENCE_TRACKER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_INFERENCE_TRACKER_HH

#include <gcs/innards/assertion_hints.hh>
#include <gcs/innards/inference_tracker-fwd.hh>
#include <gcs/innards/justification.hh>
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

        auto track(ProofLogger * const logger, const Inference inf, const Literal & lit, const Justification & just, const ReasonFunction & reason, const std::optional<AssertionAnnotation> & assertion_hints = std::nullopt) -> void
        {
            return static_cast<Actual_ *>(this)->track_impl(logger, inf, lit, just, reason, assertion_hints);
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

        auto infer(ProofLogger * const logger, const Literal & lit, const Justification & why, const ReasonFunction & reason, const std::optional<AssertionAnnotation> & assertion_hints = std::nullopt) -> void
        {
            track(logger, _state.infer(lit), lit, why, reason, assertion_hints);
        }

        [[noreturn]] auto contradiction(ProofLogger * const logger, const Justification & why, const ReasonFunction & reason, const std::optional<AssertionAnnotation> & assertion_hints = std::nullopt) -> void
        {
            if (logger)
                logger->infer(FalseLiteral{}, why, reason, assertion_hints);
            throw TrackedPropagationFailed{};
        }

        template <IntegerVariableIDLike VarType_>
        auto infer(ProofLogger * const logger, const VariableConditionFrom<VarType_> & lit, const Justification & why, const ReasonFunction & reason, const std::optional<AssertionAnnotation> & assertion_hints = std::nullopt) -> void
        {
            track(logger, _state.infer(lit), lit, why, reason, assertion_hints);
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const ReasonFunction & reason, const std::optional<AssertionAnnotation> & assertion_hints = std::nullopt) -> void
        {
            track(logger, _state.infer_equal(var, value), var == value, why, reason, assertion_hints);
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_not_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const ReasonFunction & reason, const std::optional<AssertionAnnotation> & assertion_hints = std::nullopt) -> void
        {
            track(logger, _state.infer_not_equal(var, value), var != value, why, reason, assertion_hints);
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_less_than(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const ReasonFunction & reason, const std::optional<AssertionAnnotation> & assertion_hints = std::nullopt) -> void
        {
            track(logger, _state.infer_less_than(var, value), var < value, why, reason, assertion_hints);
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_greater_than_or_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const ReasonFunction & reason, const std::optional<AssertionAnnotation> & assertion_hints = std::nullopt) -> void
        {
            track(logger, _state.infer_greater_than_or_equal(var, value), var >= value, why, reason, assertion_hints);
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_not_in_range(ProofLogger * const logger, const VarType_ & var, Integer lo, Integer hi, const Justification & why, const ReasonFunction & reason, const std::optional<AssertionAnnotation> & assertion_hints = std::nullopt) -> void
        {
            // The conclusion is the ordinary range condition; the state update
            // batches the whole removal into one erase_range pass.
            if (lo > hi)
                return;
            track(logger, _state.infer_not_in_range(var, lo, hi), not_in_range(var, lo, hi), why, reason, assertion_hints);
        }

        auto infer_all(ProofLogger * const logger, const std::vector<Literal> & lits, const Justification & why, const ReasonFunction & reason, const std::optional<AssertionAnnotation> & assertion_hints = std::nullopt) -> void
        {
            // For JustifyExplicitlyThenRUP: enter the temporary proof level once,
            // run the explicit scaffolding once, then RUP each inference under the
            // shared scaffolding. Without this, each infer() would enter and exit
            // its own temporary level, wiping the scaffolding before subsequent
            // inferences can use it.
            if (logger && ! logger->using_assertions() && std::holds_alternative<JustifyExplicitlyThenRUP>(why)) {
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

                const auto & j = std::get<JustifyExplicitlyThenRUP>(why);
                auto t = logger->temporary_proof_level();
                j.add_proof_steps(reason);
                for (const auto & lit : lits)
                    infer(logger, lit, JustifyUsingRUP{}, reason);
                logger->forget_proof_level(t);
            }
            else {
                for (const auto & lit : lits)
                    infer(logger, lit, why, reason, assertion_hints);
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

        auto track_impl(ProofLogger * const, const Inference inf, const Literal & lit, const Justification &, const ReasonFunction &, const std::optional<AssertionAnnotation> &) -> void
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

        auto track_impl(ProofLogger * const logger, const Inference inf, const Literal & lit, const Justification & just, const ReasonFunction & reason, const std::optional<AssertionAnnotation> & assertion_hints = std::nullopt) -> void
        {
            switch (inf) {
            case Inference::NoChange:
                break;

            case Inference::InteriorValuesChanged:
            case Inference::BoundsChanged:
            case Inference::Instantiated:
                if (logger)
                    logger->infer(lit, just, reason, assertion_hints);

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
                    logger->infer(lit, just, reason, assertion_hints);
                _did_anything_since_last_call_by_propagation_queue = true;
                _did_anything_since_last_call_inside_propagator = true;
                throw TrackedPropagationFailed{};
            }
        }
    };
}

#endif
