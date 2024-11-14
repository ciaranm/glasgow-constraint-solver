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

    class InferenceTracker
    {
    private:
        State & state;
        std::deque<std::pair<SimpleIntegerVariableID, Inference>> inferences;

    public:
        explicit InferenceTracker(State & s) :
            state(s)
        {
        }

        InferenceTracker(const InferenceTracker &) = delete;

        auto operator=(const InferenceTracker &) -> InferenceTracker & = delete;

        auto track(ProofLogger * const logger, const Inference inf, const Literal & lit, const Justification & just, const Reason & reason) -> void
        {
            switch (inf) {
            case Inference::NoChange:
                break;

            case Inference::InteriorValuesChanged:
            case Inference::BoundsChanged:
            case Inference::Instantiated:
                if (logger)
                    logger->infer(state, false, lit, just, reason);

                overloaded{
                    [&](const TrueLiteral &) {},
                    [&](const FalseLiteral &) {},
                    [&](const IntegerVariableCondition & cond) {
                        overloaded{
                            [&](const ConstantIntegerVariableID &) {},
                            [&](const SimpleIntegerVariableID & var) {
                                inferences.emplace_back(var, inf);
                            },
                            [&](const ViewOfIntegerVariableID & var) {
                                inferences.emplace_back(var.actual_variable, inf);
                            }}
                            .visit(cond.var);
                    }}
                    .visit(lit);
                break;

            [[unlikely]] case Inference::Contradiction:
                if (logger)
                    logger->infer(state, true, lit, just, reason);
                throw TrackedPropagationFailed{};
            }
        }

        auto infer(ProofLogger * const logger, const Literal & lit, const Justification & why, const Reason & reason) -> void
        {
            track(logger, state.infer(lit), lit, why, reason);
        }

        [[noreturn]] auto contradiction(ProofLogger * const logger, const Justification & why, const Reason & reason) -> void
        {
            if (logger)
                logger->infer(state, true, FalseLiteral{}, why, reason);
            throw TrackedPropagationFailed{};
        }

        template <IntegerVariableIDLike VarType_>
        auto infer(ProofLogger * const logger, const VariableConditionFrom<VarType_> & lit, const Justification & why, const Reason & reason) -> void
        {
            track(logger, state.infer(lit), lit, why, reason);
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const Reason & reason) -> void
        {
            track(logger, state.infer_equal(var, value), var == value, why, reason);
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_not_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const Reason & reason) -> void
        {
            track(logger, state.infer_not_equal(var, value), var != value, why, reason);
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_less_than(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const Reason & reason) -> void
        {
            track(logger, state.infer_less_than(var, value), var < value, why, reason);
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_greater_than_or_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const Reason & reason) -> void
        {
            track(logger, state.infer_greater_than_or_equal(var, value), var >= value, why, reason);
        }

        auto infer_all(ProofLogger * const logger, const std::vector<Literal> & lits, const Justification & why, const Reason & reason) -> void
        {
            bool first = true;

            // only do explicit justifications once
            Justification just_not_first{NoJustificationNeeded{}};
            visit([&](const auto & j) -> void {
                if constexpr (std::is_same_v<std::decay_t<decltype(j)>, JustifyExplicitly>)
                    just_not_first = JustifyUsingRUP{};
                else
                    just_not_first = why;
            },
                why);

            for (const auto & lit : lits) {
                infer(logger, lit, first ? why : just_not_first, reason);
                first = false;
            }
        }

        auto each_inference() const -> std::generator<std::pair<SimpleIntegerVariableID, Inference>>
        {
            return [](const auto & inferences) -> std::generator<std::pair<SimpleIntegerVariableID, Inference>> {
                for (const auto & [var, inf] : inferences)
                    co_yield std::pair{var, inf};
            }(inferences);
        }
    };
}

#endif
