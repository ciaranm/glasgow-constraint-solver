#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CIRCUIT_SUBCIRCUIT_BASE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CIRCUIT_SUBCIRCUIT_BASE_HH

#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/state.hh>

#include <map>
#include <optional>
#include <vector>

namespace gcs::innards::subcircuit
{
    /**
     * \brief The four position rows written for one edge i -> j.
     *
     * Circuit needs only one pair per edge, because its tour has a fixed anchor (node 0)
     * and so the wrap-around edge is known statically. Here the anchor is whichever node
     * is `first`, which is not known until the membership literals are fixed, so both
     * cases have to be written and the propagator's certificate splits over them.
     */
    struct EdgePosLines
    {
        // (succ[i] = j [and not first[j]]) -> pos[j] - pos[i] = 1
        std::optional<ProofLine> step_le;
        std::optional<ProofLine> step_ge;
        // (succ[i] = j [and first[j]]) -> pos[j] - pos[i] + |tour| = 1
        std::optional<ProofLine> wrap_le;
        std::optional<ProofLine> wrap_ge;
    };

    /**
     * \brief The position encoding SubCircuit::define_proof_model() writes, and the proof
     * lines the propagator's justifications cite.
     *
     * `pos[i]` is node i's index along the tour, counting from whichever node is `first`;
     * a node off the tour is given position **zero**, so the positions are not a
     * permutation, and `pos[i] >= 1` already says node i is on the tour. Nothing needs them
     * distinct: an off-tour node takes part in no position row at all, and all these rows
     * have to do is leave `pos` determined by the successors under unit propagation, which
     * is what solution checking needs. define_proof_model() says more about why, including
     * what the permutation the stdlib decomposition does build would be good for.
     *
     * Empty when proof logging is off; `defined` says which.
     */
    struct SubCircuitPosData
    {
        bool defined = false;
        // Set when the caller named a node already known to be on the tour. Then the tour
        // is anchored there, only the edges into it carry a wrap row, and there are no
        // `first` flags at all -- Circuit's shape, which it gets by anchoring on node 0.
        std::optional<long> anchor;
        std::map<long, ProofOnlySimpleIntegerVariableID> pos;
        // first[i]: node i is on the tour and every lower-numbered node is off it. At most
        // one of these holds, and exactly one does unless the tour is empty.
        std::map<long, ProofFlag> first;
        // first[i] -> pos[i] = 0
        std::map<long, ProofLine> first_is_zero;
        std::map<long, std::map<long, EdgePosLines>> edges;
    };

    /**
     * \brief The backtrackable state the SubCircuit propagators keep, allocated by
     * SubCircuit::prepare() and handed to whichever algorithm is installed.
     */
    struct SubCircuitStateHandles
    {
        ConstraintStateHandle unassigned;
    };
}

#endif // GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CIRCUIT_SUBCIRCUIT_BASE_HH
