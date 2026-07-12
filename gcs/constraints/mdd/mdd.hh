#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MDD_MDD_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MDD_MDD_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/state.hh>
#include <gcs/variable_id.hh>

#include <memory>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>

namespace gcs
{
    /**
     * \brief Constrain that the sequence of variables corresponds to a path
     * through a layered Multi-valued Decision Diagram (MDD).
     *
     * The MDD has `vars.size() + 1` layers. Layer 0 contains a single root node
     * (index 0). For each `i` in `0..vars.size()-1`, `layer_transitions[i]` is
     * indexed by source-node index within layer `i`, and maps a value to the
     * index of a target node within layer `i+1`. An assignment to `vars` is
     * accepted iff following the transitions from the root reaches one of
     * `accepting_terminals` in the final layer.
     *
     * `nodes_per_layer[i]` gives the number of nodes in layer `i` (so
     * `nodes_per_layer.size() == vars.size() + 1`).
     *
     * This is a strict generalisation of `Regular`: a DFA is an MDD whose
     * layers all share the same node set and transition function.
     *
     * Proof scaffolding uses the upfront pattern shared with Knapsack and
     * BinPacking Stage 3: the OPB encoding is the natural per-(node, val)
     * forward chains plus per-layer exactly-one, and a one-shot Top-level
     * initialiser derives per-val backward chains and statically-dead-node
     * lines. The per-call propagator's `~state[i][q]` derivations then
     * RUP-close through that scaffolding instead of re-emitting the
     * per-(parent, val) intermediate aggregations on every propagation
     * call.
     *
     * This upfront strategy is the sole proof-emission path, chosen on the
     * evidence: it wins on both proof size (7–9× smaller) and VeriPB verify
     * time (4–5× faster) over the earlier per-call strategy that emitted the
     * per-(parent, val) aggregations on every call. A per-call opt-in toggle
     * (the counterpart to `BinPacking`'s `upfront_proof = false`) is
     * therefore deliberately *not* offered here: unlike BinPacking, whose
     * per-call sweep is a self-contained bare-RUP prune, MDD's per-call
     * emission is the substantial `decrement_outdeg` / `decrement_indeg`
     * aggregation machinery, so resurrecting it behind a toggle would
     * reintroduce ~150 lines of divergent proof-emission code for a strategy
     * that loses on every measured axis. The full per-call implementation
     * remains available on the `mdd-propagator` (#205) base branch for
     * benchmarking should the trade-off ever need re-measuring.
     *
     * \ingroup Constraints
     */
    class MDD : public Constraint
    {
    private:
        struct Bridge;

        const std::vector<IntegerVariableID> _vars;
        const std::vector<std::vector<std::unordered_map<Integer, long>>> _layer_transitions;
        const std::vector<long> _nodes_per_layer;
        const std::vector<long> _accepting_terminals;
        std::shared_ptr<Bridge> _bridge;
        innards::ConstraintStateHandle _graph_idx;
        innards::ConstraintStateHandle _dead_cache_idx;
        std::vector<std::set<Integer>> _opb_alphabet;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit MDD(std::vector<IntegerVariableID> vars, std::vector<std::vector<std::unordered_map<Integer, long>>> layer_transitions,
            std::vector<long> nodes_per_layer, std::vector<long> accepting_terminals);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
