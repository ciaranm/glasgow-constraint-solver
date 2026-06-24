#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_HINTS_HH

#include <gcs/constraint_id.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state-fwd.hh>

#include <optional>
#include <string_view>
#include <utility>

namespace gcs::innards::hints
{
    /**
     * \brief linear equality's base assertion hint: just the owning constraint.
     *
     * Carried by every linear-equality inference -- the bound tightenings driven by
     * propagate_linear and the inconsistency / unit detections. All RUP-derivable,
     * so no emit_justification and no subhint; the default `(constraint_id
     * <originator>)` wire form.
     *
     * \ingroup Innards
     */
    struct LinearEquality
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "linear_equality";
    };

    /**
     * \brief linear inequality's base assertion hint: just the owning constraint.
     *
     * \ingroup Innards
     */
    struct LinearInequality
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "linear_inequality";
    };

    /**
     * \brief linear not-equals' base assertion hint: just the owning constraint.
     *
     * Carried by propagate_linear_not_equals' single-unset pruning and its
     * all-fixed contradiction. Both RUP-derivable, so no subhint and the default
     * `(constraint_id <originator>)` wire form.
     *
     * \ingroup Innards
     */
    struct LinearNotEquals
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "linear_not_equals";
    };

    /**
     * \brief linear inequality's "the condition is forced" hint, carried in a
     * reified verdict.
     *
     * Extends the base with the `cond` subhint and the emit context justify_cond
     * reads: the sanitised coefficient vector (deduced by tidy_up_linear, hence the
     * template) and the two definition lines, with the State by pointer (the verdict
     * is consumed synchronously while the constraint is live). The data is held for
     * emit_justification only; with no own hint_sexpr the hint takes the default
     * identity-plus-subhint wire form.
     *
     * \ingroup Innards
     */
    template <typename CoeffVars_>
    struct LinearInequalityCond : LinearInequality
    {
        static constexpr std::string_view subhint_name = "cond";
        const State * state;
        CoeffVars_ coeff_vars;
        std::pair<std::optional<ProofLine>, std::optional<ProofLine>> proof_lines;
    };

    template <typename CoeffVars_>
    auto emit_justification(ProofLogger & logger, const LinearInequalityCond<CoeffVars_> & cond, const ReasonLiterals & reason) -> void;
}

#endif
