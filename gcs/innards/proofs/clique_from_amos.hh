#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_CLIQUE_FROM_AMOS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_CLIQUE_FROM_AMOS_HH

#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>

#include <variant>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief Deliberate corruptions of a clique derivation, for testing only.
     *
     * \ingroup Innards
     */
    namespace clique_mutation
    {
        /// Emit the honest derivation.
        struct None
        {
        };

        /// Leave one at-most-one out of the final merge. Note what this does
        /// and does not do: the `pol` still lands on a perfectly *sound* line,
        /// just a weaker one, so nothing rejects until the returned line's
        /// content is pinned. Needs at least three members to have a merge to
        /// corrupt.
        struct DropAnAtMostOne
        {
        };

        /// Claim the members are all inactive rather than at most one active
        /// --- the "bound + 1 must fail" check for a rule whose content is a
        /// number.
        struct ClaimOneMore
        {
        };

        /// Sum every at-most-one at once and divide by `k - 1`, instead of the
        /// induction. Not a corruption so much as the derivation everyone tries
        /// first: it is *correct* for two and three members and wrong from four
        /// on, where it lands on `ceil(k/2)` instead of `k - 1`. Keeping it
        /// runnable is what stops the induction looking like unnecessary
        /// ceremony.
        struct NaiveOneShot
        {
        };

        /// Leave the division off the last merge. The line is then *stronger*
        /// than the clique inequality rather than weaker --- and the pin
        /// rejects it anyway, because an implication check is syntactic and
        /// cannot see an equivalence that needs dividing to spot. Kept because
        /// that is a surprising property to be relying on, and is what a future
        /// rearrangement of this arithmetic is most likely to break. Needs at
        /// least three members.
        struct SkipFinalDivision
        {
        };
    }

    using CliqueMutation = std::variant<clique_mutation::None, clique_mutation::DropAnAtMostOne, clique_mutation::ClaimOneMore,
        clique_mutation::NaiveOneShot, clique_mutation::SkipFinalDivision>;

    /**
     * \brief Merge the pairwise at-most-ones of a clique into the clique
     * inequality: given `~a_p + ~a_q >= 1` for every pair, derive
     * `sum over members of a_p <= 1`.
     *
     * Cutting planes can do this, but not in one step. Summing all `k(k-1)/2`
     * at-most-ones gives `(k-1) * sum ~a_p >= k(k-1)/2`, and dividing by `k-1`
     * gives `sum ~a_p >= ceil(k/2)` --- which is the answer for `k` of two or
     * three and wrong from four on. So the derivation is the classic induction,
     * growing the clique one member at a time: with the inequality for the
     * first `m` members in hand, add the `m` at-most-ones tying member `m` to
     * them, plus `m - 1` copies of the inequality so far, and divide by `m`:
     *
     *     m*~a_m + sum_{i<m} ~a_i                >= m            (the m pairs)
     *             (m-1) * sum_{i<m} ~a_i         >= (m-1)^2      (m-1 copies)
     *     ------------------------------------------------------------------
     *     m * ( ~a_m + sum_{i<m} ~a_i )          >= m + (m-1)^2
     *
     * and since `m + (m-1)^2 = m(m-1) + 1`, dividing by `m` rounds the degree up
     * to exactly `m`, which is the inequality for `m + 1` members. That spare
     * `+1` is the whole margin --- one less and the division would round down to
     * `m - 1` and the induction would not advance. It is why this works where
     * summing everything at once does not.
     *
     * `at_most_ones[j]` holds `j` lines, one per pair `(i, j)` with `i < j`,
     * indexed by `i` --- the lower triangle, in the order the induction consumes
     * it. Each must really be the at-most-one for that pair; nothing here can
     * check that, and a line that is something else will simply produce a
     * different result.
     *
     * The returned line is pinned to `sum a_p <= 1` with an `ia` step before it
     * comes back, and that step is not decoration. Dropping an input, or
     * mis-scaling a merge, leaves the `pol` on a weaker but still sound line
     * that VeriPB is right to accept --- so without the pin there is no
     * mutation of this derivation that can be caught, and the caller has no
     * guarantee that what it got says what it wanted.
     *
     * The pin is also stricter than "weaker fails". An implication check is
     * syntactic, so it rejects a line that is *equivalent* to the target but
     * differently shaped, and even one that is strictly stronger: leaving the
     * division off the last merge gives `m*(sum ~a) >= m(m-1)+1`, which implies
     * the clique inequality mathematically and does not pin
     * (\ref clique_mutation::SkipFinalDivision covers it). The final division
     * is therefore load-bearing twice over, and any rearrangement of this
     * arithmetic that changes the shape of the last line will break the pin
     * even if it stays sound. On the other hand the pin *normalises*: `ia`
     * enters the target as a new line and that is what comes back, so a caller
     * always receives the literal-exact clique inequality.
     *
     * Two things it cannot check, which are the caller's to get right: that
     * `members` are pairwise distinct (a repeat becomes a coefficient-two term
     * and means something else entirely), and that each line really is the
     * at-most-one for its pair rather than some other line that happens to
     * carry the arithmetic.
     *
     * Every intermediate is emitted at `level`. Only the returned line needs to
     * outlive the call, so a caller replaying this across a scheduling horizon
     * should think about deriving the intermediates at `ProofLevel::Temporary`
     * and forgetting them: `k^2/2` permanently-live constraints per time point
     * is a tax on every later unhinted RUP in the proof.
     *
     * Writes only derivations: no ProofModel is reachable from here, so nothing
     * can add to the OPB.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto derive_clique_from_amos(ProofLogger &, const std::vector<ProofLiteralOrFlag> & members,
        const std::vector<std::vector<ProofLine>> & at_most_ones, ProofLevel, CliqueMutation mutation = clique_mutation::None{}) -> ProofLine;
}

#endif
