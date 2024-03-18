#ifndef GLASGOW_CONSTRAINT_SOLVER_CIRCUIT_PREVENT_HH
#define GLASGOW_CONSTRAINT_SOLVER_CIRCUIT_PREVENT_HH

#include <gcs/constraints/circuit/circuit_base.hh>

namespace gcs
{
    /**
     * Circuit constraint that propagates by identifying chains and removing the head of each chain from the domain of
     * the tail "preventing" small cycles.
     */
    class CircuitPrevent : public innards::circuit::CircuitBase
    {
    public:
        using CircuitBase::CircuitBase;
        [[nodiscard]] auto clone() const -> std::unique_ptr<Constraint> override;
        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
    };
}
#endif // GLASGOW_CONSTRAINT_SOLVER_CIRCUIT_PREVENT_HH
