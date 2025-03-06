#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_GCC_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_GCC_HH

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{

    /**
     * \brief GlobalCardinalityBC Constrain that among the variables `_vars`, the value `_vals[i]` occurs `_counts[i]` times.
     * This is a somewhat hacked implementation that only achieves bounds consistency by using the LPJustifier also for propagation.
     *
     * \ingroup Constraints
     * \sa Element
     */
    class GlobalCardinalityBC : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _vars;
        std::vector<Integer> * _vals;
        std::vector<IntegerVariableID> _counts;

    public:
        explicit GlobalCardinalityBC(std::vector<IntegerVariableID> vars,
            std::vector<Integer> * vals,
            std::vector<IntegerVariableID> counts);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };

    using GlobalCardinality = GlobalCardinalityBC;
    // If someone wants to implement a better GCC propagator in the future

}

#endif
