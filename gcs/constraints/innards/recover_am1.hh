#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_RECOVER_AM1_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_RECOVER_AM1_HH

#include <gcs/innards/proofs/proof_logger.hh>

#include <functional>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief Derive a global at-most-one proof line over <em>n</em> atoms from
     * their <em>n(n-1)/2</em> pairwise at-most-one lines.
     *
     * Given a set of atoms <em>a_0, ..., a_{n-1}</em>, this emits a single
     * proof line folding together the pairwise lines supplied by the caller
     * via the <code>pair_ne</code> callback. The fold itself never looks at the
     * atoms' polarity, only at the pairwise lines, and the callers use two
     * conventions for them:
     *
     * - <b>positive atoms</b>, <em>a_k</em> = <code>x == v</code>
     *   (<code>GlobalCardinality</code>): <code>pair_ne(a_i, a_j)</code>
     *   returns <em>&not;a_i + &not;a_j &ge; 1</em>, and the result is the
     *   at-most-one <em>&Sigma; a_k &le; 1</em>, i.e. <em>&Sigma; &not;a_k
     *   &ge; n - 1</em>;
     * - <b>negated atoms</b>, <em>a_k</em> = <code>x != v</code>
     *   (<code>Among</code>): <code>pair_ne(a_i, a_j)</code> returns
     *   <em>a_i + a_j &ge; 1</em>, and the result is <em>&Sigma; a_k &ge;
     *   n - 1</em>, the at-most-one over the atoms' negations.
     *
     * Only one step depends on which: the short cut for two atoms that are
     * FalseLiteral (issue #171, in the implementation) is sound under the negated convention
     * only, where two false atoms really do violate the at-most-one. Under the
     * positive one they satisfy it, and the short cut's <em>0 &ge; 1</em> is
     * not RUP (issue #1046).
     *
     * The caller is responsible for the pairwise step. How that line is
     * derived is constraint-specific; every current caller's OPB encoding
     * makes it directly RUP-derivable (see <code>among.cc</code>).
     * <code>disjunctive.cc</code>, whose pairwise lines need a multi-step
     * <code>pol</code>, folds them with <code>recover_am1_from_pairs</code>
     * instead.
     *
     * Internally the helper folds the pairwise lines together using a
     * single <code>pol</code> expression of size <em>O(n<sup>2</sup>)</em>,
     * using division to renormalise coefficients to 1. The result is a PB
     * normal-form line whose literal coefficients are all 1.
     *
     * If two atoms are a complementary literal pair (the same underlying proof
     * literal with opposite polarity, e.g. <em>b</em> and <em>&not;b</em> from a
     * bit-aliased two-value variable), the generic fold is not tight, so the
     * helper switches to a dedicated derivation. Its result is then the PB
     * normal form of the at-most-one after the pair folds to a constant:
     * <em>&Sigma;<sub>k not in pair</sub> &not;a_k &ge; n - 2</em>, which is
     * equivalent to <em>&Sigma; &not;a_k &ge; n - 1</em> (for positive atoms;
     * with negated atoms, read <em>a_k</em> for <em>&not;a_k</em>). (See issue #557: the
     * loose generic result left a residual literal that broke aggregating pols in
     * <code>GlobalCardinality</code>. Only a caller that passes several
     * conditions on one variable can produce such a pair: that is
     * <code>GlobalCardinality</code>, and <code>Among</code>, whose atoms are
     * one variable's <code>x != v</code> over the values of interest.)
     *
     * The result line is emitted at the requested <code>ProofLevel</code>
     * (typically <code>Top</code> when the helper is called from an
     * initialiser and the result is cached for reuse, or
     * <code>Temporary</code> when it's derived on demand).
     *
     * \param logger  Proof logger to emit the pol line through.
     * \param level   Proof level for the emitted at-most-one line.
     * \param atoms   The <em>n</em> atoms participating in the at-most-one.
     *                <em>n &ge; 2</em> is required.
     * \param pair_ne Callback supplying, for each unordered pair, a line
     *                number for the pairwise at-most-one.
     * \return The line number of the global at-most-one line.
     * \throws UnexpectedException if <code>atoms.size() &lt; 2</code>.
     */
    template <typename Literal_>
    [[nodiscard]] auto recover_am1(ProofLogger & logger, ProofLevel level, const std::vector<Literal_> & atoms,
        const std::function<auto(const Literal_ &, const Literal_ &)->ProofLine> & pair_ne) -> ProofLine;
}

#endif
