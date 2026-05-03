#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_EQUALS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_EQUALS_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/reification.hh>
#include <gcs/innards/reason.hh>
#include <gcs/constraints/innards/reified_state.hh>
#include <gcs/reification.hh>
#include <gcs/variable_condition.hh>
#include <gcs/variable_id.hh>
#include <string>

namespace gcs
{
    namespace innards
    {
        auto enforce_equality(ProofLogger * const logger, const auto & v1, const auto & v2, const State & state,
            auto & inference, const Reason & reason) -> PropagatorState;
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
        innards::EvaluatedReificationCondition _evaluated_cond = innards::evaluated_reif::Deactivated{};

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        ReifiedEquals(const IntegerVariableID v1, const IntegerVariableID v2, ReificationCondition cond, bool neq = false);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const std::string & name, const innards::ProofModel * const) const -> std::string override;
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
