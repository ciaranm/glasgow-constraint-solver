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

namespace gcs::innards::circuit
{
    /**
     * \brief The "prevent" circuit propagator, shared by CircuitPrevent's install and used by the
     * collapsed Circuit constraint. Runs the value-consistent all-different, then incrementally folds
     * newly-fixed edges into chain endpoints to forbid (or force) short cycles. Defined in
     * circuit_prevent.cc.
     */
    auto propagate_circuit_using_prevent(const std::vector<IntegerVariableID> & succ, const ConstraintID & owner, const PosVarDataMap & pos_var_data,
        const ConstraintStateHandle & unassigned_handle, const ConstraintStateHandle & chain_handle, const State & state, auto & inference,
        ProofLogger * const logger) -> void;
}
#endif // GLASGOW_CONSTRAINT_SOLVER_CIRCUIT_PREVENT_HH
