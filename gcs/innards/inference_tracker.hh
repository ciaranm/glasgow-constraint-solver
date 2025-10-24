#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_INFERENCE_TRACKER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_INFERENCE_TRACKER_HH

#include <gcs/innards/inference_tracker-fwd.hh>
#include <gcs/innards/justification.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/state.hh>

#include <algorithm>
#include <deque>
#include <type_traits>
#include <utility>

#if __has_cpp_attribute(__cpp_lib_generator)
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

        auto track(ProofLogger * const logger, const Inference inf, const Literal & lit, const Justification & just, const ReasonFunction & reason) -> void
        {
            return static_cast<Actual_ *>(this)->track_impl(logger, inf, lit, just, reason);
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

        auto infer(ProofLogger * const logger, const Literal & lit, const Justification & why, const ReasonFunction & reason) -> void
        {
            track(logger, _state.infer(lit), lit, why, reason);
        }

        [[noreturn]] auto contradiction(ProofLogger * const logger, const Justification & why, const ReasonFunction & reason) -> void
        {
            if (logger)
                logger->infer(FalseLiteral{}, why, reason);
            throw TrackedPropagationFailed{};
        }

        template <IntegerVariableIDLike VarType_>
        auto infer(ProofLogger * const logger, const VariableConditionFrom<VarType_> & lit, const Justification & why, const ReasonFunction & reason) -> void
        {
            track(logger, _state.infer(lit), lit, why, reason);
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const ReasonFunction & reason) -> void
        {
            track(logger, _state.infer_equal(var, value), var == value, why, reason);
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_not_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const ReasonFunction & reason) -> void
        {
            track(logger, _state.infer_not_equal(var, value), var != value, why, reason);
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_less_than(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const ReasonFunction & reason) -> void
        {
            track(logger, _state.infer_less_than(var, value), var < value, why, reason);
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_greater_than_or_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const ReasonFunction & reason) -> void
        {
            track(logger, _state.infer_greater_than_or_equal(var, value), var >= value, why, reason);
        }

        auto infer_all(ProofLogger * const logger, const std::vector<Literal> & lits, const Justification & why, const ReasonFunction & reason) -> void
        {
            // only do explicit justifications once, but note that infer might not
            // actually call the justification if nothing is inferred
            auto just = visit([&](const auto & j) -> Justification {
                if constexpr (std::is_same_v<std::decay_t<decltype(j)>, JustifyExplicitly>)
                    return JustifyExplicitly{[done = false, &j](const ReasonFunction & reason) mutable -> void {
                        if (! done) {
                            j.add_proof_steps(reason);
                            done = true;
                        }
                    }};
                else
                    return j;
            },
                why);

            for (const auto & lit : lits)
                infer(logger, lit, just, reason);
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

        auto track_impl(ProofLogger * const, const Inference inf, const Literal & lit, const Justification &, const ReasonFunction &) -> void
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

        auto track_impl(ProofLogger * const logger, const Inference inf, const Literal & lit, const Justification & just, const ReasonFunction & reason) -> void
        {
            switch (inf) {
            case Inference::NoChange:
                break;

            case Inference::InteriorValuesChanged:
            case Inference::BoundsChanged:
            case Inference::Instantiated:
                if (logger)
                    logger->infer(lit, just, reason);

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
                    logger->infer(lit, just, reason);
                _did_anything_since_last_call_by_propagation_queue = true;
                _did_anything_since_last_call_inside_propagator = true;
                throw TrackedPropagationFailed{};
            }
        }
    };
}

#endif
