#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_INFERENCE_TRACKER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_INFERENCE_TRACKER_HH

#include <gcs/innards/inference_tracker-fwd.hh>
#include <gcs/innards/justification.hh>
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

        auto infer(const Literal & lit, const Justification & why) -> void
        {
            track(state.infer(lit, why));
        }

        auto infer_true(const Justification & why) -> void
        {
            state.infer_true(why);
        }

        auto infer_false(const Justification & why) -> void
        {
            state.infer_false(why);
            track(Inference::Contradiction);
        }

        template <IntegerVariableIDLike VarType_>
        auto infer(const VariableConditionFrom<VarType_> & lit, const Justification & why) -> void
        {
            track(state.infer(lit, why));
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_equal(const VarType_ & var, Integer value, const Justification & why) -> void
        {
            track(state.infer_equal(var, value, why));
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_not_equal(const VarType_ & var, Integer value, const Justification & why) -> void
        {
            track(state.infer_not_equal(var, value, why));
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_less_than(const VarType_ & var, Integer value, const Justification & why) -> void
        {
            track(state.infer_less_than(var, value, why));
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_greater_than_or_equal(const VarType_ & var, Integer value, const Justification & why) -> void
        {
            track(state.infer_greater_than_or_equal(var, value, why));
        }

        auto infer_all(const std::vector<Literal> & lit, const Justification & why) -> void
        {
            track(state.infer_all(lit, why));
        }
    };
}

#endif
