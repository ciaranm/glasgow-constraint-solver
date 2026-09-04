#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_AM1_FROM_PAIRS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_AM1_FROM_PAIRS_HH

#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>

#include <optional>
#include <variant>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief Deliberate corruptions of a clique derivation, for testing only.
     *
     * \ingroup Innards
     */
    namespace am1_from_pairs_mutation
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
        /// number. The only one of these that is purely about the pin: it
        /// leaves the derivation alone, so there is nothing for a downstream
        /// consumer to reject.
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

    using Am1FromPairsMutation = std::variant<am1_from_pairs_mutation::None, am1_from_pairs_mutation::DropAnAtMostOne,
        am1_from_pairs_mutation::ClaimOneMore, am1_from_pairs_mutation::NaiveOneShot, am1_from_pairs_mutation::SkipFinalDivision>;

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
     * that VeriPB is right to accept, so nothing *here* catches it and the
     * caller has no guarantee that what it got says what it wanted.
     *
     * Whether anything catches it *later* is the caller's to know, and so far
     * the answer has always been yes. Every call site here consumes the clique
     * line coefficient by coefficient --- a counting `pol` that needs an exact
     * cancellation, and whose RUP then fails when it does not get one --- so a
     * weakened merge is rejected downstream whether or not it was pinned. That
     * was measured rather than assumed. With the pin replaced by an unpinned
     * copy of whatever the induction landed on, the `DropAnAtMostOne`,
     * `NaiveOneShot` and `SkipFinalDivision` mutations were each still
     * rejected: at `subcircuit.cc` (#797), and at all three of
     * `all_different/justify.cc`, `sort/sort.cc` and
     * `min_distance/min_distance.cc` (#805).
     *
     * What that leaves the pin doing here is saying so locally, where it can
     * name the line that is wrong, instead of as a RUP failure a few hundred
     * lines further on --- and covering a caller who is *not*
     * coefficient-sensitive, for whom it would be the only thing between a
     * quietly weakened derivation and a proof that verifies. So the pin stays;
     * it is one line, and a caller should not have to know which kind it is.
     * But do not read a mutation rejected at your own call site as evidence
     * that the pin is what rejected it: run the experiment. `ClaimOneMore`
     * cannot answer it for you, since it corrupts nothing but the pin's target
     * and so has nothing left to catch once the pin is gone.
     *
     * The pin is also stricter than "weaker fails". An implication check is
     * syntactic, so it rejects a line that is *equivalent* to the target but
     * differently shaped, and even one that is strictly stronger: leaving the
     * division off the last merge gives `m*(sum ~a) >= m(m-1)+1`, which implies
     * the clique inequality mathematically and does not pin
     * (\ref am1_from_pairs_mutation::SkipFinalDivision covers it). The final division
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
     * `guard`, if given, is a literal every input at-most-one carries as an
     * extra disjunct --- `~a_p + ~a_q + g >= 1` --- so that what is being
     * derived is "at most one of these, *or* the guard". None of the arithmetic
     * changes: the guard rides through the induction, and its coefficient stays
     * equal to the degree at every step, because a merge takes `m` copies of it
     * from the pairs and `m - 1` from the copies of `current`, and that same
     * `m(m-1) + 1` divides by `m` to the same `m`. So the pin at `k` members is
     * `sum a_p <= 1 + (k-1) g`, written with the guard negated to keep every
     * coefficient positive, and it is as strict as the unguarded one. What the
     * caller has to remember is that the coefficient grows with the clique: a
     * sum of folds over cliques of different sizes carries `sum (k_f - 1)` of
     * the guard, and getting back to a coefficient of one means dividing by
     * exactly that.
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
    [[nodiscard]] auto recover_am1_from_pairs(ProofLogger &, const std::vector<ProofLiteralOrFlag> & members,
        const std::vector<std::vector<ProofLine>> & at_most_ones, ProofLevel, const std::optional<ProofLiteralOrFlag> & guard = std::nullopt,
        Am1FromPairsMutation mutation = am1_from_pairs_mutation::None{}) -> ProofLine;
}

#endif
