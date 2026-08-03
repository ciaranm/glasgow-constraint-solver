#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_SUBSET_SUM_STRENGTHENING_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_SUBSET_SUM_STRENGTHENING_HH

#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/integer.hh>

#include <variant>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief One term of a subset-sum strengthening: a strictly positive
     * coefficient and the 0/1 term it weights.
     *
     * \ingroup Innards
     */
    struct SubsetSumItem
    {
        Integer coefficient;
        ProofLiteralOrFlag term;
    };

    /**
     * \brief Deliberate corruptions of a subset-sum strengthening, for testing
     * only.
     *
     * The strengthened line is only worth having if it is tight, and a proof
     * that verifies does not say that on its own: if the derivation has slack,
     * a wrong bound verifies too. Each of these breaks one part of it in a way
     * that must make VeriPB reject --- either the derivation itself, or the
     * consumer's use of the line it returns.
     *
     * \ingroup Innards
     */
    namespace subset_sum_mutation
    {
        /// Emit the honest derivation.
        struct None
        {
        };

        /// Claim one better than the largest reachable sum. The final
        /// domination step is then unsupported.
        struct ClaimOneBetter
        {
        };

        /// Leave out one layer's state transitions, so the layer's
        /// at-least-one has nothing to stand on.
        struct SkipALayer
        {
        };

        /// Take the divisibility fast path with a divisor that does not divide
        /// every coefficient. The division is still a sound proof step --- it
        /// just does not establish the claimed bound, which shows up in the
        /// consumer rather than here.
        struct BogusDivisor
        {
        };
    }

    using SubsetSumMutation = std::variant<subset_sum_mutation::None, subset_sum_mutation::ClaimOneBetter, subset_sum_mutation::SkipALayer,
        subset_sum_mutation::BogusDivisor>;

    /**
     * \brief What derive_subset_sum_strengthening() established.
     *
     * \ingroup Innards
     */
    struct SubsetSumStrengthening
    {
        /// The strengthened line, `sum of coefficient * term <= bound`. When
        /// nothing could be strengthened this is the source line itself, not a
        /// vacuous re-derivation of it.
        ProofLine line;
        /// The bound the line carries: the largest subset sum of the
        /// coefficients that is at most the input bound.
        Integer bound;
        /// Whether the divisibility fast path applied.
        bool by_division;
    };

    /**
     * \brief The largest subset sum of `coefficients` that is at most `bound`.
     *
     * A word-parallel bitset subset-sum, so O(n * bound / 64). Coefficients
     * must be strictly positive, and the bound non-negative.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto largest_subset_sum_at_most(const std::vector<Integer> & coefficients, Integer bound) -> Integer;

    /**
     * \brief Strengthen a derived line by integrality: given `source` saying
     * `sum of coefficient * term <= bound`, derive the same sum bounded by the
     * largest subset sum of the coefficients that is at most `bound`.
     *
     * The two lines have the same 0/1 solutions --- every value the sum can
     * take is a subset sum, so no assignment lies in the gap --- but the
     * strengthened one is a tighter inequality, which is what makes it worth
     * deriving: it is what later cutting-planes arithmetic can use. This is the
     * integrality argument behind a knapsack-augmented overload check's
     * availability bound (issue #550), Schulz's capacity reduction (#547) and
     * single-resource lifting certificates (#549).
     *
     * Two derivations, chosen automatically:
     *
     * - **Divisibility.** When `d`, the gcd of every coefficient, exceeds one
     *   and `d * floor(bound / d)` is the answer, two pol steps do it:
     *   divide by `d`, multiply back. This is Chvatal-Gomory rounding, and it
     *   is what applies whenever the coefficients share a factor.
     * - **Layered dynamic programming.** Otherwise, one layer per item, with
     *   three reified flags per reachable partial sum (`>= v`, `<= v`, and
     *   their conjunction), the transitions between layers derived as clauses
     *   from the flags' own reification halves, and one at-least-one per layer
     *   saying the partial sum is in some reachable state. The last layer's
     *   at-least-one, whose states are all at most the answer by construction,
     *   is what dominates the strengthened line. Size is O(n * bound) flags in
     *   the worst case, so a caller working with a large bound should budget
     *   for it (and reach for this only where it pays).
     *
     * Writes only derivations: the API has no access to a ProofModel, so it
     * cannot add to the OPB even by mistake. `level` selects where they land
     * --- `Temporary` inside a conflict justification, `Top` for a presolver.
     *
     * Degenerate cases: an empty item list gives a bound of zero; a bound that
     * is already reachable returns the source line unchanged; a bound at least
     * the sum of every coefficient gives that sum.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto derive_subset_sum_strengthening(ProofLogger &, const std::vector<SubsetSumItem> & items, ProofLine source, Integer bound,
        ProofLevel level, SubsetSumMutation mutation = subset_sum_mutation::None{}) -> SubsetSumStrengthening;
}

#endif
