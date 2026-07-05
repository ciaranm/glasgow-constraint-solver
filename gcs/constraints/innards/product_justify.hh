#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_PRODUCT_JUSTIFY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_PRODUCT_JUSTIFY_HH

#include <gcs/constraints/innards/product_encoding.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/reason.hh>

#include <optional>
#include <vector>

namespace gcs::innards::product_justify
{
    /**
     * \brief A derived sign-case-conditional bound: under the ambient reason
     * and the `cases` literals, `sum >= rhs` holds, materialised at `line`
     * (at ProofLevel::Temporary). The justification procedures pass these
     * between steps instead of re-deriving reified normal forms; the raw pol
     * shapes combine fine, which is what the thesis derivations do on paper.
     *
     * \ingroup Innards
     */
    struct ConditionalBound
    {
        WPBSum sum;
        Integer rhs;
        HalfReifyOnConjunctionOf cases;
        ProofLine line;
    };

    /**
     * \brief Derive `reason => +/-v >= b` as a proof line (RUP off the order
     * encoding, in V-form so it cancels against the V-form channel rows).
     * `lower` selects +v >= b, otherwise -v >= -b is derived from v <= b.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto derive_operand_bound(ProofLogger &, const ReasonLiterals & reason, SimpleIntegerVariableID v, bool lower, Integer bound)
        -> ConditionalBound;

    /**
     * \brief Thesis Justification Subprocedure 7.3, cake flavour: channel a
     * signed operand bound to a bound on the slot's magnitude, conditional on
     * the slot's sign-case literal. For the non-negative branch ([v>=0]) a
     * lower bound on v is a lower bound on mag; for the negative branch
     * ([v<0]) a lower bound on v is an UPPER bound on mag (and vice versa),
     * so the returned bound's direction flips. One pol add against the
     * matching channel row; the sign-case literal is always kept in `cases`
     * (dead cases are closed by RUP in the sign-case combination instead of
     * being special-cased away here).
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto channel_bound_to_magnitude(ProofLogger &, const ConditionalBound & operand_bound, SimpleIntegerVariableID v,
        const product_enc::MagnitudeChannel & channel, bool negative_branch) -> ConditionalBound;

    /**
     * \brief Thesis Justification Subprocedure 7.1: from magnitude lower
     * bounds `a_lb` on |a| and `b_lb` on |b| (both non-negative), derive
     * `Sum 2^(i+j) prod_ij >= a_lb * b_lb` by pure cutting planes, O(n*m)
     * lines. The result's cases are the union of the operands' cases.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto grid_sum_lower_bound(ProofLogger &, const ReasonLiterals & reason, const product_enc::BitProductGrid & grid,
        const SimpleOrProofOnlyIntegerVariableID & bits_a, const ConditionalBound & a_lb, const ConditionalBound & b_lb) -> ConditionalBound;

    /**
     * \brief Thesis Justification Subprocedure 7.2: from magnitude upper
     * bounds on |a| and |b|, derive `-Sum 2^(i+j) prod_ij >= -a_ub * b_ub`.
     * Needs a small proof-by-contradiction subproof per grid row; the
     * per-cell W-lines are derived once and cached in the grid's cells.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto grid_sum_upper_bound(ProofLogger &, const ReasonLiterals & reason, product_enc::BitProductGrid & grid,
        const SimpleOrProofOnlyIntegerVariableID & bits_a, const SimpleOrProofOnlyIntegerVariableID & bits_b, const ConditionalBound & a_ub,
        const ConditionalBound & b_ub) -> ConditionalBound;

    /**
     * \brief Channel a grid-sum bound to a bound on the signed result via the
     * matching mag_Z row (thesis Subprocedure 7.4, cake flavour): the sign of
     * the case (product of the operand case signs) picks the row and flips
     * the direction for a negative result; the result's sign atom is
     * discharged by RUP off the sign clauses under the cases.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto channel_grid_bound_to_result(ProofLogger &, const ReasonLiterals & reason, SimpleIntegerVariableID v3,
        const product_enc::ResultChannel & channel, const ConditionalBound & grid_bound, bool result_negative, bool lower) -> ConditionalBound;

    /**
     * \brief Conclude an inference from its per-case refutations: one
     * red-with-empty-witness derivation of `reason => conclusion`, whose
     * subproof derives a clause per case (each premise added to the negated
     * goal), closes dead and zero cases by RUP, and combines everything with
     * the fixed nested saturating cut (thesis ResolveSigns), never a search.
     * Pass the premises with their `cases` intact; the conclusion literal is
     * then established by the caller's ThenRUP.
     *
     * \ingroup Innards
     */
    auto conclude_by_sign_cases(
        ProofLogger &, const ReasonLiterals & reason, const WPBSumLE & conclusion, const std::vector<ConditionalBound> & premises) -> void;
}

#endif
