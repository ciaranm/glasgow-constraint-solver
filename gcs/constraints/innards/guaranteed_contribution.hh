#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_GUARANTEED_CONTRIBUTION_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_GUARANTEED_CONTRIBUTION_HH

#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/reason.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs::innards
{
    /**
     * \brief What a variable-height task is guaranteed to contribute at one
     * time point, stated over the contribution bits a capacity row actually
     * carries.
     *
     * A constant-height task's load in <code>C<sub>t</sub></code> is
     * <code>h·active</code>, a coefficient on a flag, and anything reasoning
     * about a window's activity cancels against it directly. A variable height
     * is nonlinear, so it is linearised over per-bit contribution flags and
     * <code>C<sub>t</sub></code> carries <code>Σ 2<sup>k</sup>·cc<sub>k</sub></code>
     * instead. This derives
     *
     * <blockquote>
     * <code>Σ<sub>k</sub> 2<sup>k</sup>·cc<sub>k</sub> + bound·~active &ge; bound</code>
     * </blockquote>
     *
     * --- "either the task is not active here, or it contributes at least
     * <code>bound</code>" --- which is the bridge between the two forms.
     * Added to a capacity row with coefficient one, the bits cancel exactly and
     * what is left on the task is <code>bound·active</code>; summed over a
     * window against an activity bound, it converts the whole of that bound
     * into contribution terms.
     *
     * It is a RUP rather than a <code>pol</code>, and that is not laziness:
     * negating it forces <code>~active</code> to zero, and what remains is the
     * <code>cge</code> row and the height's lower bound over two power-of-two
     * bit counters, which unit propagation walks down a bit at a time. Every
     * step is single-constraint, so any fixpoint finds it --- swept over
     * several thousand (bound, upper bound, bit width) shapes, including
     * contribution bits narrower than the height's, before being believed. The
     * <code>pol</code> it replaces would be the <code>cge</code> row plus the
     * bound, then a saturate to cap the reification constant down to the bound,
     * then a literal axiom per bit to put the coefficients back.
     *
     * <code>bound</code> is the height's lower bound, and which one is the
     * caller's business: the <em>declared</em> one is a model fact, and a
     * weaker number the moment anything has tightened it. Either way the unit
     * saying the atom holds is what makes the row unconditional, and that comes
     * from <code>need_gevar</code>'s boundary pin where the bound is the
     * declared one and from a RUP where it is not --- so <code>reason</code>
     * must entail the bound whenever it is not the declared one, and may be
     * null where the caller knows it is.
     *
     * <code>contribution_ge_row</code> is the labelled <code>cge</code> row
     * saying <code>active ⇒ contrib &ge; h</code>, which the caller looks up
     * against whichever constraint published it.
     *
     * Hinted with exactly the three facts the argument uses, where the height's
     * atom has a defining line. A zero-one height resolves to a bare literal
     * instead, which a hint list cannot carry, so that one goes unhinted ---
     * slower to check and no less true.
     */
    [[nodiscard]] auto guaranteed_contribution_row(ProofLogger &, const ReasonLiterals * reason, const std::vector<ProofFlag> & contribution_bits,
        const ProofFlag & active, const SimpleIntegerVariableID & height, Integer bound, ProofLine contribution_ge_row, ProofLevel) -> ProofLine;
}

#endif
