#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_EQUALS_MUTATIONS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_EQUALS_MUTATIONS_HH

#include <variant>

/**
 * \file
 *
 * Deliberate corruptions of the equals family's proof steps, which exist so
 * that a test can show its derivations are tight to what they claim. They live
 * here, in the innards, rather than beside the constraint they corrupt: a
 * header a user of the library includes should not advertise a way to make the
 * solver emit deliberately wrong proofs. Issue #869, and the same reason
 * CumulativeProofMutation and Am1FromPairsMutation are here.
 *
 * Why the family needs this more than most rather than less. Almost every
 * inference here is a single RUP against a two-row OPB encoding, and "veripb
 * accepted a one-line RUP" is the weakest evidence in the suite: an over-broad
 * conclusion can be RUP for a reason that has nothing to do with the rule that
 * drew it. Solutions matching brute force does not help either, since a
 * corrupted *proof* changes no answers. So before this, nothing anywhere
 * demonstrated that VeriPB refuses a mangled equals derivation.
 *
 * Each of these changes the proof and nothing else: the same inferences are
 * made, the same solutions reported, and the OPB is untouched.
 *
 * **Measured.** VeriPB rejects all six of the lanes registered for these, and
 * the control lane checks that the same four instances verify when they are not
 * corrupted -- so the family's derivations are tight, which is what issue #869
 * asked. What took work was the instances, not the corruptions, and in a way
 * that generalises to the next family:
 *
 *  - Dropping a reason literal is only a corruption when that literal traces to
 *    a **search decision**. A fact some propagator derived is written to the
 *    proof as a clause of its own, so the checker has it whether or not the
 *    reason repeats it, and a root-firing rule's reason is a restatement of the
 *    database. Both of the obvious no-overlap instances -- an interleaved pair
 *    of domains, and the same with one bound pushed by an unconditional
 *    LessThanEqual -- accept the mutation for exactly that reason. The lane's
 *    instance puts the bound push behind a decision instead.
 *  - Omitting the bridge lemmas is caught at almost every domain width, and not
 *    at two of them: over `{0..w}` with the middle third removed, VeriPB accepts
 *    the lemma-free proof at w = 5 and w = 11 and rejects it at 6, 7, 8, 9, 10,
 *    12, 14, 16, 20, 100 and 1000. Both exceptions have an interval endpoint on
 *    a bit boundary, where the bound is one literal rather than a sum and unit
 *    propagation can cross the equality unaided. So the lemmas are load-bearing
 *    in general, and a narrow fixture would have said they were not.
 */

namespace gcs::innards
{
    /**
     * \brief Deliberate corruptions of the equals family's derivations, for
     * testing only. VeriPB must reject each of them.
     *
     * A mutation that still verifies is a finding about the honest derivation,
     * not about the mutation.
     *
     * Two of the four kinds of thing that could go wrong here are reasons and
     * two are emitted lemmas, which between them cover the family's whole
     * proof surface -- there is nothing else. One candidate from issue #869 is
     * deliberately absent: "cite the wrong half of the equality" has no site,
     * because no step in this family cites a proof line by label at all. Every
     * one is a RUP, which is why the reason and the lemmas are the only places
     * a mistake can live.
     *
     * \ingroup Innards
     */
    namespace equals_proof_mutation
    {
        /// Emit the honest derivations.
        struct None
        {
        };

        /// Leave the fixed operand's value out of the reason for forcing the
        /// other operand to it, so the pruning is claimed to follow from the
        /// reification condition alone. Shows the reason is minimal in the sense
        /// that matters: the equality rows say the operands agree, not what
        /// either of them is.
        struct DropFixedOperandReason
        {
        };

        /// Leave the last literal out of the no-overlap witness's reason. That
        /// literal is the walk's stop -- the one fact saying the position the
        /// walk has climbed to is past the top of one of the two domains -- so
        /// without it the reason establishes a lower bound and never that the
        /// bound is impossible. The last rather than the first because the
        /// witness re-walks the reason it was given (#870), and a reason with no
        /// anchor is not a corrupt derivation but an unreadable one.
        struct DropNoOverlapStopLiteral
        {
        };

        /// Emit no bound lemmas before a `~[pruned in lo..hi]` conclusion, so it
        /// is claimed to be RUP against the equality on its own. This is the
        /// mutation that tests a design claim rather than an arithmetic step: a
        /// range literal asserts only order atoms while the equality rows are a
        /// bit-sum, which is the entire reason
        /// justify_not_in_range_across_equality exists. If VeriPB accepts this,
        /// that helper is unnecessary here.
        struct OmitBridgeLemmas
        {
        };

        /// Emit no lemmas at all in the no-overlap witness, leaving the walk's
        /// interval literals to be seen through by unit propagation unaided.
        /// The control for the rule: it says whether the walk is load-bearing
        /// before asking whether any particular move of it is.
        struct OmitNoOverlapLemmas
        {
        };

        /// Emit the no-overlap witness's lemmas under `cond` instead of
        /// `! cond`, which is the one-character version of the mistake that is
        /// easiest to make in a reified derivation and the hardest to see by
        /// reading: the lemmas are still about the right operands, the right
        /// bounds and the right direction, and every one of them is false.
        struct FlipNoOverlapSelector
        {
        };
    }

    using EqualsProofMutation =
        std::variant<equals_proof_mutation::None, equals_proof_mutation::DropFixedOperandReason, equals_proof_mutation::DropNoOverlapStopLiteral,
            equals_proof_mutation::OmitBridgeLemmas, equals_proof_mutation::OmitNoOverlapLemmas, equals_proof_mutation::FlipNoOverlapSelector>;
}

#endif
