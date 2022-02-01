/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ELEMENT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ELEMENT_HH

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    class Element : public Constraint
    {
    private:
        IntegerVariableID _var, _idx_var;
        const std::vector<IntegerVariableID> & _vals;

    public:
        explicit Element(IntegerVariableID var, IntegerVariableID idx_var, const std::vector<IntegerVariableID> & vals);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(Propagators &, const State &) && -> void override;
    };

    class Element2DConstantArray : public Constraint
    {
    private:
        IntegerVariableID _var, _idx1, _idx2;
        const std::vector<std::vector<Integer>> & _vals;

    public:
        explicit Element2DConstantArray(IntegerVariableID var, IntegerVariableID idx1, IntegerVariableID idx2,
            const std::vector<std::vector<Integer>> & vals);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(Propagators &, const State &) && -> void override;
    };
}

#endif
