#ifndef GLASGOW_CONSTRAINT_SOLVER_CIRCUIT_SCC_HH
#define GLASGOW_CONSTRAINT_SOLVER_CIRCUIT_SCC_HH

#include <gcs/constraint.hh>
#include <gcs/constraints/circuit/circuit_base.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>
#include <gcs/variable_id.hh>
#include <vector>

namespace gcs
{
    /**
     * \brief SCC-only tuning knobs for the Circuit constraint, set through Circuit's
     * with_prune_root()/with_prune_skip()/... fluent setters.
     */
    struct SCCOptions
    {
        bool prune_root = true;
        bool prune_skip = true;
        bool fix_req = true;
        bool prune_within = true;
        bool prove_using_dominance = false;
        bool enable_comments = true;
        bool prove_am1_by_contradiction = true;
        bool short_reasons = true;
    };
}

namespace gcs::innards::circuit
{
    /**
     * \brief The SCC-based circuit propagator, used by the Circuit constraint when the
     * circuit::SCC algorithm is selected. Runs the value-consistent all-different, checks
     * strongly connected components (pruning edges that cannot lie on a Hamiltonian cycle),
     * and prevents small cycles. Defined in circuit_scc.cc.
     */
    auto propagate_circuit_using_scc(const State & state, auto & inference, ProofLogger * const logger, const ReasonLiterals & reason,
        const ConstraintID & owner, const std::vector<IntegerVariableID> & succ, const SCCOptions & scc_options,
        const ConstraintStateHandle & pos_var_data_handle, const ConstraintStateHandle & proof_flag_data_handle,
        const ConstraintStateHandle & pos_alldiff_data_handle, const ConstraintStateHandle & unassigned_handle) -> void;

    /**
     * \brief Set up the backtrackable state for the SCC circuit propagator and install it, given
     * the position-variable proof data already produced by Circuit::set_up. Called from
     * Circuit::install when the circuit::SCC algorithm is selected. Defined in circuit_scc.cc.
     */
    auto install_circuit_scc(Propagators & propagators, State & initial_state, const ConstraintID & owner,
        const std::vector<IntegerVariableID> & succ, const SCCOptions & scc_options, PosVarDataMap pos_var_data) -> void;
}

#endif // GLASGOW_CONSTRAINT_SOLVER_CIRCUIT_SCC_HH
