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
     * \brief Install the "prevent" circuit propagator over the backtrackable state
     * Circuit::prepare() allocated (the unassigned set plus the incremental chain endpoints)
     * and the position-variable proof data Circuit::define_proof_model() produced. Called from
     * Circuit::install_propagators() when the circuit::Prevent algorithm is selected. Defined
     * in circuit_prevent.cc.
     */
    auto install_circuit_prevent(Propagators & propagators, const ConstraintID & owner, const std::vector<IntegerVariableID> & succ,
        PosVarDataMap pos_var_data, const CircuitStateHandles & handles) -> void;

    // Incremental "prevent" state: the fixed successor edges partition the nodes into
    // simple paths (chains). For each node we record the chain it belongs to by its
    // endpoints. These are maintained in O(1) as edges are fixed and restored on
    // backtrack (held as backtrackable constraint state), rather than recomputed from
    // scratch each call. orig[v] is valid when v is a chain *end*, dest[v]/len[v] when
    // v is a chain *start* -- which is exactly how they are queried below.
    struct PreventChainData
    {
        std::vector<long> orig;      // start node of the chain ending at this node
        std::vector<long> dest;      // end node of the chain starting at this node
        std::vector<long> len;       // number of fixed edges in the chain starting at this node
        std::vector<long> unspliced; // node indices whose fixed successor edge is not yet folded in
    };

    /**
     * \brief The initial incremental small-cycle chain endpoints for n nodes: each node
     * starts as its own length-zero chain, and edges fold in as successors are fixed.
     * Built here so Circuit::prepare() can allocate the constraint state that holds it.
     */
    [[nodiscard]] auto make_prevent_chain_data(std::size_t n) -> PreventChainData;
}
#endif // GLASGOW_CONSTRAINT_SOLVER_CIRCUIT_PREVENT_HH
