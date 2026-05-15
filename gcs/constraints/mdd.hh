#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MDD_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MDD_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/state.hh>
#include <gcs/variable_id.hh>
#include <set>
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
     * \ingroup Constraints
     */
    class MDD : public Constraint
    {
    private:
        const std::vector<IntegerVariableID> _vars;
        const std::vector<std::vector<std::unordered_map<Integer, long>>> _layer_transitions;
        const std::vector<long> _nodes_per_layer;
        const std::vector<long> _accepting_terminals;
        std::vector<std::vector<innards::ProofFlag>> _state_at_pos_flags;
        innards::ConstraintStateHandle _graph_idx;
        std::vector<std::set<Integer>> _opb_alphabet;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit MDD(std::vector<IntegerVariableID> vars,
            std::vector<std::vector<std::unordered_map<Integer, long>>> layer_transitions,
            std::vector<long> nodes_per_layer,
            std::vector<long> accepting_terminals);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
