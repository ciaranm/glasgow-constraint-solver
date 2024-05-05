#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_INFERENCE_TRACKER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_INFERENCE_TRACKER_HH

#include <gcs/innards/inference_tracker-fwd.hh>
#include <gcs/innards/justification.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/state.hh>

#include <type_traits>
#include <utility>
#include <vector>

namespace gcs::innards
{
    class TrackedPropagationFailed
    {
    };

    class InferenceTracker
    {
    private:
        State & state;

    public:
        std::vector<std::pair<Literal, HowChanged>> changes;

        explicit InferenceTracker(State & s) :
            state(s)
        {
        }

        InferenceTracker(const InferenceTracker &) = delete;

        auto operator=(const InferenceTracker &) -> InferenceTracker & = delete;

        auto track(const Literal & lit, HowChanged how) -> void
        {
            switch (how) {
            case HowChanged::Unchanged:
                break;
            case HowChanged::BoundsChanged:
            case HowChanged::InteriorValuesChanged:
            case HowChanged::Instantiated:
                changes.emplace_back(lit, how);
                break;
            [[unlikely]] case HowChanged::Contradiction:
                throw TrackedPropagationFailed{};
            }
        }

        auto infer(ProofLogger * const logger, const Literal & lit, const Justification & why, const Reason & reason) -> void
        {
            track(lit, state.infer(logger, lit, why, reason));
        }

        [[noreturn]] auto infer_false(ProofLogger * const logger, const Justification & why, const Reason & reason) -> void
        {
            state.infer_false(logger, why, reason);
            throw TrackedPropagationFailed{};
        }

        template <IntegerVariableIDLike VarType_>
        auto infer(ProofLogger * const logger, const VariableConditionFrom<VarType_> & lit, const Justification & why, const Reason & reason) -> void
        {
            track(lit, state.infer(logger, lit, why, reason));
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const Reason & reason) -> void
        {
            track(var == value, state.infer_equal(logger, var, value, why, reason));
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_not_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const Reason & reason) -> void
        {
            track(var != value, state.infer_not_equal(logger, var, value, why, reason));
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_less_than(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const Reason & reason) -> void
        {
            track(var < value, state.infer_less_than(logger, var, value, why, reason));
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_greater_than_or_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const Reason & reason) -> void
        {
            track(var >= value, state.infer_greater_than_or_equal(logger, var, value, why, reason));
        }

        auto infer_all(ProofLogger * const logger, const std::vector<Literal> & lits, const Justification & why,
            const Reason & reason) -> void
        {
            bool first = true;

            // only do explicit justifications once
            Justification just_not_first{NoJustificationNeeded{}};
            if (logger)
                visit([&](const auto & j) -> void {
                    if constexpr (std::is_same_v<std::decay_t<decltype(j)>, JustifyExplicitly>)
                        just_not_first = JustifyUsingRUP{};
                    else
                        just_not_first = why;
                },
                    why);

            for (const auto & lit : lits) {
                if (first)
                    infer(logger, lit, why, reason);
                else
                    infer(logger, lit, just_not_first, reason);
                first = false;
            }
        }
    };
}

#endif
