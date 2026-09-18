#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PLUS_MINUS_GAC_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PLUS_MINUS_GAC_HH

#include <gcs/constraint_id.hh>
#include <gcs/constraints/innards/plus_minus_mutations.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/variable_id.hh>

#include <optional>
#include <utility>

namespace gcs::innards
{
    /**
     * \brief Which row the GAC arm is propagating: `a + b == result` for
     * Plus, `a - b == result` for Minus.
     *
     * \ingroup Innards
     */
    enum class PlusMinusRow
    {
        Plus,
        Minus
    };

    /**
     * \brief Install the consistency::GAC arm shared by Plus and Minus.
     *
     * Prunes each variable to the values the other two can sum or subtract to,
     * computed over intervals (Minkowski sums), so the work depends on how many
     * intervals the domains have and never on how wide they are. One pass is the
     * GAC fixpoint whenever the three variables are distinct.
     *
     * The row is propagated over the user's own three variables with signed
     * coefficients rather than by rewriting Minus as Plus over a `-b` view:
     * the proof's `pol` steps work by each operand's terms cancelling against
     * the model's row, which is stated over the user's `b`, and a synthesised
     * view would not cancel (this is how Minus broke in `2ec1297e`).
     *
     * The sum lines are the model's two halves, as Plus::define_proof_model
     * and Minus::define_proof_model return them. The mutation is for testing
     * only; see PlusMinusProofMutation.
     *
     * \ingroup Innards
     */
    auto install_plus_minus_gac(Propagators & propagators, const ConstraintID & owner, PlusMinusRow row, IntegerVariableID a, IntegerVariableID b,
        IntegerVariableID result, const std::pair<std::optional<ProofLine>, std::optional<ProofLine>> & sum_line,
        PlusMinusProofMutation mutation = plus_minus_proof_mutation::None{}) -> void;
}

#endif
