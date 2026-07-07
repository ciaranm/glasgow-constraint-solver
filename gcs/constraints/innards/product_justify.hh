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
    [[nodiscard]] auto derive_operand_bound(ProofLogger &, const ReasonLiterals & reason, IntegerVariableID v, bool lower, Integer bound,
        ProofLevel result_level = ProofLevel::Temporary) -> ConditionalBound;

    /**
     * \brief As derive_operand_bound, but under an assumed atom rather than
     * the reason: `[v>=b] => v >= b` (or the upper-bound mirror), the atom
     * kept in `cases`. This is how the factor-bound justifications assume the
     * refuted excluded range (thesis Procedures 7.6/7.7): the driver's
     * negated goal supplies the atom as a unit.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto derive_assumed_operand_bound(
        ProofLogger &, IntegerVariableID v, bool lower, Integer bound, ProofLevel result_level = ProofLevel::Temporary) -> ConditionalBound;

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
    [[nodiscard]] auto channel_bound_to_magnitude(ProofLogger &, const ConditionalBound & operand_bound, IntegerVariableID v,
        const product_enc::MagnitudeChannel & channel, bool negative_branch, bool strengthen_nonzero = false) -> ConditionalBound;

    /**
     * \brief Thesis Justification Subprocedure 7.1: from magnitude lower
     * bounds `a_lb` on |a| and `b_lb` on |b| (both non-negative), derive
     * `Sum 2^(i+j) prod_ij >= a_lb * b_lb` by pure cutting planes, O(n*m)
     * lines. The result's cases are the union of the operands' cases.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto grid_sum_lower_bound(ProofLogger &, const ReasonLiterals & reason, const product_enc::BitProductGrid & grid,
        const SimpleOrProofOnlyIntegerVariableID & bits_a, const ConditionalBound & a_lb, const ConditionalBound & b_lb,
        ProofLevel result_level = ProofLevel::Temporary) -> ConditionalBound;

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
        const ConditionalBound & b_ub, ProofLevel result_level = ProofLevel::Temporary) -> ConditionalBound;

    /**
     * \brief Channel a grid-sum bound to a bound on the signed result via the
     * matching mag_Z row (thesis Subprocedure 7.4, cake flavour): the sign of
     * the case (product of the operand case signs) picks the row and flips
     * the direction for a negative result; the result's sign atom is
     * discharged by RUP off the sign clauses under the cases.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto channel_grid_bound_to_result(ProofLogger &, const ReasonLiterals & reason, IntegerVariableID v3,
        const product_enc::ResultChannel & channel, const ConditionalBound & grid_bound, bool result_negative, bool lower,
        const std::vector<ProofLine> & claim_hints = {}) -> ConditionalBound;

    /**
     * \brief The defining proof line for an atomic condition, if it has one
     * (a primitive atom, say a declared domain boundary, does not). Used as
     * `ia` antecedents and assembled into RUP hint sets, which restrict the
     * checker's propagation to the given lines and so must be complete.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto def_line_for(ProofLogger &, const IntegerVariableCondition &) -> std::optional<ProofLine>;

    /**
     * \brief Append the definition lines a unit-propagation chain through an
     * atomic condition can touch: the condition's own definition and its
     * negation's, and for (in)equality atoms the order-atom definitions they
     * bridge to (the eq0 rows connect [v=0] with [v>=0] and [v>=1]).
     *
     * \ingroup Innards
     */
    auto add_condition_def_hints(ProofLogger &, const IntegerVariableCondition &, std::vector<ProofLine> & hints) -> void;

    /**
     * Pol-derive and hint the order-ladder clauses linking `cond`'s atom to
     * the sign-clause threshold atoms ([v>=1], [v>=0]), so a hinted RUP
     * claim can cross between order atoms of the same variable.
     */
    auto add_order_bridge_hints(ProofLogger &, const IntegerVariableCondition &, std::vector<ProofLine> & hints) -> void;

    /**
     * \brief One sign-case dimension: the two complementary atoms the case
     * split branches on ([v>=0] and [v<0] for a slot's operand).
     *
     * \ingroup Innards
     */
    struct SignCaseDimension
    {
        Literal positive_atom;
        Literal negative_atom;
    };

    /**
     * \brief Whether conclude_by_sign_cases hints its subproof RUP steps.
     * Assemble is right when the premises' sum terms cancel exactly against
     * the negated goal (product bounds through
     * channel_grid_bound_to_result), so the dead-pattern clauses and the cut
     * result close from the reason atoms, their ladders and the premise
     * lines alone. Leave None when the premises drag further encoding terms
     * into the cut (divide/modulus premises carry view bits and aux-atom
     * rows), where only a database-wide RUP reaches the closing conflict.
     *
     * \ingroup Innards
     */
    enum class SubproofRUPHints
    {
        None,
        Assemble,
    };

    /**
     * \brief Conclude an inference from its per-case bounds: one
     * red-with-empty-witness derivation of `reason => conclusion`, whose
     * subproof derives a clause per case pattern — a pol add of the case's
     * premise line onto the negated goal where a premise exists, a plain RUP
     * clause where the case is dead under the reason — then combines them
     * with the fixed nested saturating cut over the dimensions (thesis
     * ResolveSigns, made total by [v>=0]/[v<0] being complementary: no
     * separate zero cases). Never a search. premise_by_pattern is indexed by
     * bitmask over dims, bit k set meaning dim k's negative branch; its size
     * must be 2^dims.size(). Returns the derived reified conclusion line;
     * the inferred literal itself then follows by the caller's ThenRUP.
     *
     * \ingroup Innards
     */
    auto conclude_by_sign_cases(ProofLogger &, const ReasonLiterals & reason, const WPBSumLE & conclusion,
        const std::vector<SignCaseDimension> & dims, const std::vector<std::optional<ConditionalBound>> & premise_by_pattern,
        const std::vector<Literal> & zero_refutations = {}, SubproofRUPHints hint_rups = SubproofRUPHints::None) -> ProofLine;
}

#endif
