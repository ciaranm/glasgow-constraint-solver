#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_INFERENCE_TRACKER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_INFERENCE_TRACKER_HH

#include <gcs/innards/inference_tracker-fwd.hh>
#include <gcs/innards/justification.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/state.hh>

namespace gcs::innards
{
    class TrackedPropagationFailed
    {
    };

    class InferenceTracker
    {
    private:
        State & state;
        Inference inference;

    public:
        explicit InferenceTracker(State & s) :
            state(s),
            inference(Inference::NoChange)
        {
        }

        InferenceTracker(const InferenceTracker &) = delete;

        auto operator=(const InferenceTracker &) -> InferenceTracker & = delete;

        [[nodiscard]] auto inference_so_far() const -> Inference
        {
            return inference;
        }

        auto track(const Inference inf) -> void
        {
            switch (inf) {
            case Inference::NoChange: break;
            case Inference::Change:
                inference = inf;
                break;
            [[unlikely]] case Inference::Contradiction:
                throw TrackedPropagationFailed{};
            }
        }

        auto infer(ProofLogger * const logger, const Literal & lit, const Justification & why, const Reason & reason) -> void
        {
            track(state.infer(logger, lit, why, reason));
        }

        [[noreturn]] auto infer_false(ProofLogger * const logger, const Justification & why, const Reason & reason) -> void
        {
            state.infer_false(logger, why, reason);
            throw TrackedPropagationFailed{};
        }

        template <IntegerVariableIDLike VarType_>
        auto infer(ProofLogger * const logger, const VariableConditionFrom<VarType_> & lit, const Justification & why, const Reason & reason) -> void
        {
            track(state.infer(logger, lit, why, reason));
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const Reason & reason) -> void
        {
            track(state.infer_equal(logger, var, value, why, reason));
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_not_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const Reason & reason) -> void
        {
            track(state.infer_not_equal(logger, var, value, why, reason));
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_less_than(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const Reason & reason) -> void
        {
            track(state.infer_less_than(logger, var, value, why, reason));
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_greater_than_or_equal(ProofLogger * const logger, const VarType_ & var, Integer value, const Justification & why, const Reason & reason) -> void
        {
            track(state.infer_greater_than_or_equal(logger, var, value, why, reason));
        }

        auto infer_all(ProofLogger * const logger, const std::vector<Literal> & lit, const Justification & why, const Reason & reason) -> void
        {
            track(state.infer_all(logger, lit, why, reason));
        }
    };
}

#endif
