#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_EQUAL_ALL_EQUAL_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_EQUAL_ALL_EQUAL_HH

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief Constrain that vars[0] = vars[1] = ... = vars[n-1].
     *
     * Each propagator call prunes every variable to the bounds all the
     * variables share and, if any domain has holes, to the intersection of
     * every variable's domain. This is stronger per call than the equivalent
     * chain of binary Equals constraints, where bound and hole removals
     * would have to ripple along the chain via the propagation queue, one
     * step at a time. At its fixpoint it is GAC on distinct variables, but
     * one call need not reach that fixpoint: over holes a bound can land
     * inside another variable's interval and need a second call, and a
     * variable repeated through views changes under its own inferences.
     *
     * \ingroup Constraints
     */
    class AllEqual : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _vars;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit AllEqual(std::vector<IntegerVariableID> vars);

        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
