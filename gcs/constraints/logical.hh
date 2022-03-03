/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LOGICAL_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LOGICAL_HH 1

#include <gcs/constraint.hh>
#include <gcs/literal.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    class And : public Constraint
    {
    private:
        const Literals & _lits;
        const Literal & _full_reif;

    public:
        // Equivalent to And([var != 0 : var in vars], full_reif != 0)
        explicit And(const std::vector<IntegerVariableID> & vars, const IntegerVariableID & full_reif);

        explicit And(const Literals &, const Literal &);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, const innards::State &) && -> void override;
    };

    class Or : public Constraint
    {
    private:
        const Literals & _lits;
        const Literal & _full_reif;

    public:
        // Equivalent to Or([var != 0 : var in vars], full_reif != 0)
        explicit Or(const std::vector<IntegerVariableID> & vars, const IntegerVariableID & full_reif);

        explicit Or(const Literals &, const Literal &);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, const innards::State &) && -> void override;
    };
}

#endif
