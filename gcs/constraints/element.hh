/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ELEMENT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ELEMENT_HH

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief Constrain that `var = vals[idx]`.
     *
     * \ingroup Constraints
     * \sa Element2DConstantArray
     */
    class Element : public Constraint
    {
    private:
        IntegerVariableID _var, _idx;
        const std::vector<IntegerVariableID> _vals;

    public:
        explicit Element(IntegerVariableID var, IntegerVariableID idx, std::vector<IntegerVariableID> vals);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, innards::State &) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };

    /**
     * \brief Constrain that `var = vals[idx1, idx2]`.
     *
     * \ingroup Constraints
     * \sa Element
     */
    class Element2DConstantArray : public Constraint
    {
    private:
        IntegerVariableID _var, _idx1, _idx2;
        std::vector<std::vector<Integer>> _vals;

    public:
        explicit Element2DConstantArray(IntegerVariableID var, IntegerVariableID idx1, IntegerVariableID idx2,
            std::vector<std::vector<Integer>> vals);

        virtual auto describe_for_proof() -> std::string override;
        virtual auto install(innards::Propagators &, innards::State &) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };
}

#endif
