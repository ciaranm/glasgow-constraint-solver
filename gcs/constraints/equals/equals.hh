#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_EQUALS_EQUALS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_EQUALS_EQUALS_HH

#include <gcs/constraint.hh>
#include <gcs/constraints/innards/equals_mutations.hh>
#include <gcs/constraints/innards/reified_state.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/reification.hh>
#include <gcs/innards/reason.hh>
#include <gcs/lifetime.hh>
#include <gcs/reification.hh>
#include <gcs/variable_condition.hh>
#include <gcs/variable_id.hh>
#include <string>

namespace gcs
{
    namespace innards
    {
        auto enforce_equality(ProofLogger * const logger, const auto & v1, const auto & v2, const State & state, auto & inference,
            const ReasonLiterals & reason, const ConstraintID & owner, EqualsProofMutation mutation = equals_proof_mutation::None{})
            -> PropagatorState;
    }

    /**
     * \brief Constrain that two variables are equal dependent upon a reification condition.
     *
     * \ingroup Constraints
     */
    class ReifiedEquals : public Constraint
    {
    private:
        IntegerVariableID _v1, _v2;
        ReificationCondition _cond;
        bool _neq;
        innards::EqualsProofMutation _proof_mutation = innards::equals_proof_mutation::None{};
        innards::EvaluatedReificationCondition _evaluated_cond = innards::evaluated_reif::Deactivated{};

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        ReifiedEquals(const IntegerVariableID v1, const IntegerVariableID v2, ReificationCondition cond, bool neq = false);

        /// Testing only: corrupt one step of the derivations this constraint
        /// emits, so a mutation lane can check that veripb refuses the result.
        /// See innards::EqualsProofMutation. Never use this outside a test.
        auto with_proof_mutation(innards::EqualsProofMutation mutation) -> ReifiedEquals &;

        virtual auto clone() const -> std::unique_ptr<Constraint> override;

        /**
         * \name The constraint as posted.
         *
         * Public so that a presolver can read a posted Equals or NotEquals back
         * and decide whether to lift it. Over `{0, 1}` operands either is a
         * 2-XOR, which is what ParitySystemGathering wants them for; nothing in
         * these says anything about the proof output, which
         * ConstraintProofModelData is for.
         *
         * `enforces_equality()` is false for a NotEquals: the reification
         * condition alone does not say which, because MustNotHold on an Equals
         * and MustHold on a NotEquals are different spellings of the same thing
         * and only one of them is constructible.
         * @{
         */
        [[nodiscard]] auto left_variable() const -> IntegerVariableID
        {
            return _v1;
        }

        [[nodiscard]] auto right_variable() const -> IntegerVariableID
        {
            return _v2;
        }

        [[nodiscard]] auto reification_condition() const GCS_LIFETIME_BOUND -> const ReificationCondition &
        {
            return _cond;
        }

        [[nodiscard]] auto enforces_equality() const -> bool
        {
            return ! _neq;
        }
        ///@}

        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };

    /**
     * \brief Constrain that two variables are equal.
     *
     * \ingroup Constraints
     */
    class Equals : public ReifiedEquals
    {
    public:
        Equals(const IntegerVariableID v1, const IntegerVariableID v2);
    };

    /**
     * \brief Constrain that two variables are equal if `cond` holds.
     *
     * \ingroup Constraints
     */
    class EqualsIf : public ReifiedEquals
    {
    public:
        EqualsIf(const IntegerVariableID v1, const IntegerVariableID v2, IntegerVariableCondition cond);
    };

    /**
     * \brief Constrain that two variables are equal if and only if `cond` holds.
     *
     * \ingroup Constraints
     */
    class EqualsIff : public ReifiedEquals
    {
    public:
        EqualsIff(const IntegerVariableID v1, const IntegerVariableID v2, IntegerVariableCondition cond);
    };

    /**
     * \brief Constrain that two variables are not equal.
     *
     * \ingroup Constraints
     */
    class NotEquals : public ReifiedEquals
    {
    public:
        NotEquals(const IntegerVariableID v1, const IntegerVariableID v2);
    };

    /**
     * \brief Constrain that two variables are not equal if `cond` holds.
     *
     * \ingroup Constraints
     */
    class NotEqualsIf : public ReifiedEquals
    {
    public:
        NotEqualsIf(const IntegerVariableID v1, const IntegerVariableID v2, IntegerVariableCondition cond);
    };

    /**
     * \brief Constrain that two variables are not equal if and only if `cond` holds.
     *
     * \ingroup Constraints
     */
    class NotEqualsIff : public ReifiedEquals
    {
    public:
        NotEqualsIff(const IntegerVariableID v1, const IntegerVariableID v2, IntegerVariableCondition cond);
    };
}

#endif
