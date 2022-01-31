/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_EQUALITY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_EQUALITY_HH 1

#include <gcs/constraint.hh>
#include <gcs/detail/linear.hh>
#include <gcs/integer.hh>

#include <vector>

namespace gcs
{
    class LinearEquality : public Constraint
    {
    private:
        Linear _coeff_vars;
        Integer _value;
        bool _gac;

    public:
        explicit LinearEquality(Linear && coeff_vars, Integer value, bool gac = false);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(Propagators &, const State &) && -> void override;
    };

    class LinearLessEqual : public Constraint
    {
    private:
        Linear _coeff_vars;
        Integer _value;

    public:
        explicit LinearLessEqual(Linear && coeff_vars, Integer value);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(Propagators &, const State &) && -> void override;
    };
}

#endif
