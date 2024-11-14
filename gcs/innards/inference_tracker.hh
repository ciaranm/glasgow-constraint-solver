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

#include <range/v3/all.hpp>

namespace gcs::innards
{
    class TrackedPropagationFailed
    {
    };

    class InferenceTracker
    {
    private:
        State & _state;
        std::deque<std::pair<SimpleIntegerVariableID, Inference>> _inferences;
        bool _did_anything_since_last_call;

    public:
        explicit InferenceTracker(State & s) :
            _state(s),
            _did_anything_since_last_call(false)
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
                    logger->infer(_state, false, lit, just, reason);

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

                _did_anything_since_last_call = true;
                break;

            [[unlikely]] case Inference::Contradiction:
                if (logger)
                    logger->infer(_state, true, lit, just, reason);
                _did_anything_since_last_call = true;
                throw TrackedPropagationFailed{};
            }
        }

        auto infer(ProofLogger * const logger, const Literal & lit, const Justification & why, const Reason & reason) -> void
        {
            track(logger, _state.infer(lit), lit, why, reason);
        }

        [[noreturn]] auto contradiction(ProofLogger * const logger, const Justification & why, const Reason & reason) -> void
        {
            if (logger)
                logger->infer(_state, true, FalseLiteral{}, why, reason);
            throw TrackedPropagationFailed{};
        }

        template <IntegerVariableIDLike VarType_>
        auto infer(ProofLogger * const logger, const VariableConditionFrom<VarType_> & lit, const Justification & why, const Reason & reason) -> void
        {
            track(logger, _state.infer(lit), lit, why, reason);
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const Reason & reason) -> void
        {
            track(logger, _state.infer_equal(var, value), var == value, why, reason);
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_not_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const Reason & reason) -> void
        {
            track(logger, _state.infer_not_equal(var, value), var != value, why, reason);
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_less_than(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const Reason & reason) -> void
        {
            track(logger, _state.infer_less_than(var, value), var < value, why, reason);
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_greater_than_or_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const Reason & reason) -> void
        {
            track(logger, _state.infer_greater_than_or_equal(var, value), var >= value, why, reason);
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
                for (const auto & [var, inf] : inferences | ranges::views::reverse)
                    co_yield std::pair{var, inf};
            }(_inferences);
        }

        auto reset() -> void
        {
            _inferences.clear();
            _did_anything_since_last_call = false;
        }

        auto did_anything_since_last_call() -> bool
        {
            return std::exchange(_did_anything_since_last_call, false);
        }
    };
}

#endif
