#ifndef GLASGOW_CONSTRAINT_SOLVER_CIRCUIT_PREVENT_HH
#define GLASGOW_CONSTRAINT_SOLVER_CIRCUIT_PREVENT_HH

#include <gcs/constraints/circuit/circuit_base.hh>

namespace gcs::innards::circuit
{
    /**
     * \brief The "prevent" circuit propagator, used by the Circuit constraint when the
     * circuit::Prevent algorithm is selected. Runs the value-consistent all-different, then
     * incrementally folds newly-fixed edges into chain endpoints to forbid (or force) short
     * cycles. Defined in circuit_prevent.cc.
     */
    auto propagate_circuit_using_prevent(const std::vector<IntegerVariableID> & succ, const ConstraintID & owner, const PosVarDataMap & pos_var_data,
        const ConstraintStateHandle & unassigned_handle, const ConstraintStateHandle & chain_handle, const State & state, auto & inference,
        ProofLogger * const logger) -> void;

    /**
     * \brief Set up the backtrackable state for the "prevent" circuit propagator (unassigned set
     * plus the incremental chain endpoints) and install it, given the position-variable proof data
     * already produced by Circuit::set_up. Called from Circuit::install when the circuit::Prevent
     * algorithm is selected. Defined in circuit_prevent.cc.
     */
    auto install_circuit_prevent(Propagators & propagators, State & initial_state, const ConstraintID & owner,
        const std::vector<IntegerVariableID> & succ, PosVarDataMap pos_var_data) -> void;
}
#endif // GLASGOW_CONSTRAINT_SOLVER_CIRCUIT_PREVENT_HH
