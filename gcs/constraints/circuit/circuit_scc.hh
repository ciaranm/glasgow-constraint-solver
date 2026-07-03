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

    class CircuitSCC : public innards::circuit::CircuitBase
    {
    protected:
        const SCCOptions scc_options;

    public:
        explicit CircuitSCC(std::vector<IntegerVariableID> var, bool gac_all_different = false, SCCOptions scc_options = SCCOptions{});
        [[nodiscard]] auto clone() const -> std::unique_ptr<Constraint> override;
        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
    };
}

namespace gcs::innards::circuit
{
    /**
     * \brief The SCC-based circuit propagator, shared by CircuitSCC's install and used by the
     * collapsed Circuit constraint. Runs the value-consistent all-different, checks strongly
     * connected components (pruning edges that cannot lie on a Hamiltonian cycle), and prevents
     * small cycles. Defined in circuit_scc.cc.
     */
    auto propagate_circuit_using_scc(const State & state, auto & inference, ProofLogger * const logger, const ReasonLiterals & reason,
        const ConstraintID & owner, const std::vector<IntegerVariableID> & succ, const SCCOptions & scc_options,
        const ConstraintStateHandle & pos_var_data_handle, const ConstraintStateHandle & proof_flag_data_handle,
        const ConstraintStateHandle & pos_alldiff_data_handle, const ConstraintStateHandle & unassigned_handle) -> void;
}

#endif // GLASGOW_CONSTRAINT_SOLVER_CIRCUIT_SCC_HH
