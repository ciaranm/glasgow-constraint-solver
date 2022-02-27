/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_EQUALS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_EQUALS_HH

#include <gcs/constraint.hh>
#include <gcs/literal.hh>
#include <gcs/variable_id.hh>

#include <string>

namespace gcs
{
    class Equals : public Constraint
    {
    private:
        IntegerVariableID _v1, _v2;

    public:
        Equals(const IntegerVariableID v1, const IntegerVariableID v2);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, const innards::State &) && -> void override;
    };

    class EqualsIf : public Constraint
    {
    private:
        IntegerVariableID _v1, _v2;
        Literal _cond;

    public:
        EqualsIf(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, const innards::State &) && -> void override;
    };

    class EqualsIff : public Constraint
    {
    private:
        IntegerVariableID _v1, _v2;
        Literal _cond;

    public:
        EqualsIff(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, const innards::State &) && -> void override;
    };

    class NotEquals : public Constraint
    {
    private:
        IntegerVariableID _v1, _v2;

    public:
        NotEquals(const IntegerVariableID v1, const IntegerVariableID v2);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, const innards::State &) && -> void override;
    };
}

#endif
