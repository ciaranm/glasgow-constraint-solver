
#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_REIFIED_STATE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_REIFIED_STATE_HH

#include <gcs/innards/literal.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/reification.hh>
#include <gcs/variable_condition.hh>

#include <optional>
#include <variant>

namespace gcs::innards
{
    namespace evaluated_reif
    {
        /**
         * \brief The reification condition is currently TRUE: the constraint
         * must be enforced. The cond literal is provided so propagators can
         * include it in their reasons.
         */
        struct MustHold
        {
            Literal cond;
        };

        /**
         * \brief The reification condition is currently FALSE: the negation
         * of the constraint must be enforced.
         */
        struct MustNotHold
        {
            Literal cond;
        };

        /**
         * \brief The reification condition is not yet decided. The
         * cond_to_infer_if_constraint_must_*() methods say what cond literal
         * to infer for each verdict, encoding the contrapositive logic of
         * the original reification kind (If, NotIf, Iff).
         */
        struct Undecided
        {
            IntegerVariableCondition cond;
            bool set_cond_if_must_hold, set_not_cond_if_must_not_hold, set_not_cond_if_must_hold;

            /**
             * If the constraint is now known to definitely hold, the
             * literal that the reification kind says we should infer (or
             * nullopt if the kind doesn't license an inference here — for
             * instance plain `If` doesn't infer cond when the constraint
             * just happens to hold).
             */
            [[nodiscard]] auto cond_to_infer_if_constraint_must_hold() const -> std::optional<Literal>
            {
                if (set_cond_if_must_hold)
                    return cond;
                if (set_not_cond_if_must_hold)
                    return ! cond;
                return std::nullopt;
            }

            /**
             * Symmetric: literal to infer when the constraint is known to
             * definitely not hold.
             */
            [[nodiscard]] auto cond_to_infer_if_constraint_must_not_hold() const -> std::optional<Literal>
            {
                if (set_not_cond_if_must_not_hold)
                    return ! cond;
                return std::nullopt;
            }
        };

        /**
         * \brief The reification kind has been resolved to "no constraint
         * needed" (e.g. an `If(cond)` whose cond is now known FALSE).
         * Propagators do nothing.
         */
        struct Deactivated
        {
        };
    }

    using EvaluatedReificationCondition = std::variant<
        evaluated_reif::MustHold,
        evaluated_reif::MustNotHold,
        evaluated_reif::Undecided,
        evaluated_reif::Deactivated>;

    /**
     * \brief Resolve a static `ReificationCondition` against the current
     * search State to one of the runtime variants above.
     */
    [[nodiscard]] auto test_reification_condition(const State &, const ReificationCondition &)
        -> EvaluatedReificationCondition;
}

#endif
