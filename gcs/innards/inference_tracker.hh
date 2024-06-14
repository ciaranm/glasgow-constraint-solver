#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_LOGGING_INFERENCE_TRACKER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_LOGGING_INFERENCE_TRACKER_HH

#include <gcs/innards/justification.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/state.hh>

#include <type_traits>
#include <utility>
#include <vector>

namespace gcs::innards
{
    class TrackedPropagationFailed
    {
    };

    template <typename Actual_>
    class InferenceTrackerCore
    {
    public:
        InferenceTrackerCore() = default;

        InferenceTrackerCore(const InferenceTrackerCore &) = delete;

        std::vector<std::pair<Literal, HowChanged>> changes;

        auto operator=(const InferenceTrackerCore &) -> InferenceTrackerCore & = delete;

        auto infer(const Literal & lit, const Justification & why, const Reason & reason) -> void
        {
            static_cast<Actual_ *>(this)->track(lit, static_cast<Actual_ *>(this)->state.infer(lit), why, reason);
        }

        [[noreturn]] auto infer_false(const Justification & why, const Reason & reason) -> void
        {
            static_cast<Actual_ *>(this)->track(FalseLiteral{}, HowChanged::Contradiction, why, reason);
            throw TrackedPropagationFailed{};
        }

        template <IntegerVariableIDLike VarType_>
        auto infer(const VariableConditionFrom<VarType_> & lit, const Justification & why, const Reason & reason) -> void
        {
            static_cast<Actual_ *>(this)->track(lit, static_cast<Actual_ *>(this)->state.infer(lit), why, reason);
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_equal(const VarType_ & var, Integer value, const Justification & why, const Reason & reason) -> void
        {
            static_cast<Actual_ *>(this)->track(var == value, static_cast<Actual_ *>(this)->state.infer_equal(var, value), why, reason);
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_not_equal(const VarType_ & var, Integer value, const Justification & why, const Reason & reason) -> void
        {
            static_cast<Actual_ *>(this)->track(var != value, static_cast<Actual_ *>(this)->state.infer_not_equal(var, value), why, reason);
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_less_than(const VarType_ & var, Integer value, const Justification & why, const Reason & reason) -> void
        {
            static_cast<Actual_ *>(this)->track(var < value, static_cast<Actual_ *>(this)->state.infer_less_than(var, value), why, reason);
        }

        template <IntegerVariableIDLike VarType_>
        auto infer_greater_than_or_equal(const VarType_ & var, Integer value, const Justification & why, const Reason & reason) -> void
        {
            static_cast<Actual_ *>(this)->track(var >= value, static_cast<Actual_ *>(this)->state.infer_greater_than_or_equal(var, value), why, reason);
        }

        auto infer_all(const std::vector<Literal> & lits, const Justification & why,
            const Reason & reason) -> void
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
                if (first)
                    infer(lit, why, reason);
                else
                    infer(lit, just_not_first, reason);
                first = false;
            }
        }
    };

    class SimpleInferenceTracker : public InferenceTrackerCore<SimpleInferenceTracker>
    {
    public:
        State & state;

        explicit SimpleInferenceTracker(State & s) :
            state(s)
        {
        }

        SimpleInferenceTracker(const SimpleInferenceTracker &) = delete;
        SimpleInferenceTracker(SimpleInferenceTracker &&) noexcept = default;

        auto track(const Literal & lit, HowChanged how, const Justification &, const Reason &) -> void
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

        template <typename Func_>
        auto run_in_eager_mode(const Func_ & func)
        {
            return func(*this);
        }
    };

    class LogUsingGuessesInferenceTracker : public InferenceTrackerCore<LogUsingGuessesInferenceTracker>
    {
    public:
        State & state;
        ProofLogger & logger;

        explicit LogUsingGuessesInferenceTracker(State & s, ProofLogger & l) :
            state(s),
            logger(l)
        {
        }

        LogUsingGuessesInferenceTracker(const LogUsingGuessesInferenceTracker &) = delete;
        LogUsingGuessesInferenceTracker(LogUsingGuessesInferenceTracker &&) noexcept = default;

        auto guesses_reason() -> Reason
        {
            Literals guesses;
            state.for_each_guess([&](const Literal & lit) { guesses.push_back(lit); });
            return [=]() { return guesses; };
        }

        auto track(const Literal & lit, HowChanged how, const Justification & why, const Reason &) -> void
        {
            switch (how) {
            case HowChanged::Unchanged:
                break;
            case HowChanged::BoundsChanged:
            case HowChanged::InteriorValuesChanged:
            case HowChanged::Instantiated:
                logger.infer(state, false, lit, why, guesses_reason());
                changes.emplace_back(lit, how);
                break;
            [[unlikely]] case HowChanged::Contradiction:
                logger.infer(state, true, lit, why, guesses_reason());
                throw TrackedPropagationFailed{};
            }
        }

        template <typename Func_>
        auto run_in_eager_mode(const Func_ & func)
        {
            return func(*this);
        }
    };

    class LogUsingReasonsInferenceTracker : public InferenceTrackerCore<LogUsingReasonsInferenceTracker>
    {
    public:
        State & state;
        ProofLogger & logger;

        explicit LogUsingReasonsInferenceTracker(State & s, ProofLogger & l) :
            state(s),
            logger(l)
        {
        }

        LogUsingReasonsInferenceTracker(const LogUsingReasonsInferenceTracker &) = delete;
        LogUsingReasonsInferenceTracker(LogUsingReasonsInferenceTracker &&) noexcept = default;

        auto track(const Literal & lit, HowChanged how, const Justification & why, const Reason & reason) -> void
        {
            switch (how) {
            case HowChanged::Unchanged:
                break;
            case HowChanged::BoundsChanged:
            case HowChanged::InteriorValuesChanged:
            case HowChanged::Instantiated:
                logger.infer(state, false, lit, why, reason);
                changes.emplace_back(lit, how);
                break;
            [[unlikely]] case HowChanged::Contradiction:
                logger.infer(state, true, lit, why, reason);
                throw TrackedPropagationFailed{};
            }
        }

        template <typename Func_>
        auto run_in_eager_mode(const Func_ & func)
        {
            return func(*this);
        }
    };

    class LazyProofGenerationInferenceTracker : public InferenceTrackerCore<LazyProofGenerationInferenceTracker>
    {
    private:
        struct Imp;
        std::unique_ptr<Imp> _imp;

    public:
        State & state;
        ProofLogger & logger;

        explicit LazyProofGenerationInferenceTracker(State & s, ProofLogger & l);
        ~LazyProofGenerationInferenceTracker();

        LazyProofGenerationInferenceTracker(const LazyProofGenerationInferenceTracker &) = delete;
        LazyProofGenerationInferenceTracker(LazyProofGenerationInferenceTracker &&) noexcept = default;

        auto track(const Literal & lit, HowChanged how, const Justification & why, const Reason & reason) -> void;

        auto for_each_pending_proof_step(const std::function<auto(const Literal &, const Justification &, const Reason &)->void> &) -> void;

        template <typename Func_>
        auto run_in_eager_mode(const Func_ & func)
        {
            LogUsingGuessesInferenceTracker inference{state, logger};
            return func(inference);
        }
    };

    using SomeKindOfInferenceTracker = std::variant<
        SimpleInferenceTracker,
        LogUsingGuessesInferenceTracker,
        LogUsingReasonsInferenceTracker,
        LazyProofGenerationInferenceTracker>;
}

#endif
