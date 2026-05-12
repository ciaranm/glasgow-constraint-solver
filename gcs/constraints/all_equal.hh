#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_EQUAL_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_EQUAL_HH

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief Constrain that vars[0] = vars[1] = ... = vars[n-1].
     *
     * Achieves GAC in a single propagator pass by intersecting every
     * variable's domain and pruning each variable to that intersection.
     * This is strictly stronger per pass than the equivalent chain of
     * binary Equals constraints, where bound and hole removals would
     * have to ripple along the chain via the propagation queue, one
     * step at a time.
     *
     * \ingroup Constraints
     */
    class AllEqual : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _vars;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit AllEqual(std::vector<IntegerVariableID> vars);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
