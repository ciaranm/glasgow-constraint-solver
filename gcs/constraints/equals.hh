#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_EQUALS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_EQUALS_HH

#include <gcs/constraint.hh>
#include <gcs/innards/literal.hh>
#include <gcs/variable_condition.hh>
#include <gcs/variable_id.hh>

#include <string>

namespace gcs
{
    /**
     * \brief Constrain that two variables are equal.
     *
     * \ingroup Constraints
     */
    class Equals : public Constraint
    {
    private:
        IntegerVariableID _v1, _v2;

    public:
        Equals(const IntegerVariableID v1, const IntegerVariableID v2);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };

    /**
     * \brief Constrain that two variables are equal if `cond` holds.
     *
     * \ingroup Constraints
     */
    class EqualsIf : public Constraint
    {
    private:
        IntegerVariableID _v1, _v2;
        innards::Literal _cond;

    public:
        EqualsIf(const IntegerVariableID v1, const IntegerVariableID v2, innards::Literal cond);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };

    /**
     * \brief Constrain that two variables are equal if and only if `cond` holds.
     *
     * \ingroup Constraints
     */
    class EqualsIff : public Constraint
    {
    private:
        IntegerVariableID _v1, _v2;
        innards::Literal _cond;

    public:
        EqualsIff(const IntegerVariableID v1, const IntegerVariableID v2, innards::Literal cond);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };
}

#endif
