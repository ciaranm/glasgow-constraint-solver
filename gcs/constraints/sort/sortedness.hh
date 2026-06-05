#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_SORT_SORTEDNESS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_SORT_SORTEDNESS_HH

#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_model-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs::innards
{
    /**
     * \brief The proof-only witness for the sortedness relation `y = sort(x)`,
     * shared between Sort and ArgSort.
     *
     * `before[ip][i]` is the flag "x[ip] comes before x[i]" under the total order
     * (value, then original index); `before_fwd`/`before_rev` are its two
     * reification halves. `pos[i]` is the stable rank of x[i] (the position it is
     * sent to in y), defined as the sum of the `before` flags; `rank_ge[i]` /
     * `rank_le[i]` are the two halves of that defining equality. See
     * dev_docs/sortedness.md.
     */
    struct SortednessWitness
    {
        std::vector<std::vector<ProofFlag>> before;
        std::vector<std::vector<ProofLine>> before_fwd, before_rev;
        std::vector<ProofOnlySimpleIntegerVariableID> pos;
        std::vector<ProofLine> rank_ge, rank_le;
    };

    /**
     * \brief Proof-only witness for the permutation-based Sort encoding.
     *
     * `p[i][j]` is the binary flag "x[i] is placed at position j in y".
     * `row_al1[i]` is the model line for `Σ_j p[i][j] >= 1` (used as the
     * at-least-one in pigeonhole counting pols). `col_am1[j]` is the model
     * line for `-Σ_i p[i][j] >= -1` (at-most-one per column).
     */
    struct SortPermWitness
    {
        std::vector<std::vector<ProofFlag>> p;
        std::vector<ProofLine> row_al1;
        std::vector<ProofLine> col_am1;
    };

    /**
     * \brief Emit the OPB encoding of `y = sort(x)` (the compact, domain-width-
     * independent stable-rank encoding) and return its proof-only witness.
     *
     * Used by both Sort and ArgSort: Sort exposes `y` as its real output, while
     * ArgSort supplies internal `y` and additionally channels the witness to its
     * permutation. The caller must have set up `x` and `y` in the model already.
     */
    [[nodiscard]] auto define_sortedness_proof_model(ProofModel & model,
        const std::vector<IntegerVariableID> & x, const std::vector<IntegerVariableID> & y) -> SortednessWitness;

    /**
     * \brief Install the Mehlhorn-Thiel bounds-consistency propagator for
     * `y = sort(x)`, using the witness from define_sortedness_proof_model.
     */
    auto install_sortedness_propagator(Propagators & propagators,
        const std::vector<IntegerVariableID> & x, const std::vector<IntegerVariableID> & y,
        const SortednessWitness & witness) -> void;

    /**
     * \brief Permutation-based model: emit the doubly-stochastic p[i][j]
     * encoding plus the channel `p[i][j] -> y[j]=x[i]` and the y-sorted
     * constraints. Returns a SortPermWitness holding the p flags and the
     * key doubly-stochastic constraint lines needed by the propagation proofs.
     *
     * The before[ip][i] and rank[i][j] flags are also added to the OPB model
     * for UP-determinism — see dev_docs/sortedness.md.
     */
    [[nodiscard]] auto define_sort_proof_model_perm(ProofModel & model,
        const std::vector<IntegerVariableID> & x, const std::vector<IntegerVariableID> & y) -> SortPermWitness;

    /**
     * \brief Install the Mehlhorn-Thiel propagator using the permutation
     * witness, certifying every inference via direct p[i][j] pigeonhole reasoning.
     */
    auto install_sort_propagator_perm(Propagators & propagators,
        const std::vector<IntegerVariableID> & x, const std::vector<IntegerVariableID> & y,
        const SortPermWitness & witness) -> void;
}

#endif
