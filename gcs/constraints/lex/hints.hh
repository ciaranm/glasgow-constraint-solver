#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LEX_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LEX_HINTS_HH

#include <gcs/constraint_id.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/variable_id.hh>

#include <cstddef>
#include <memory>
#include <optional>
#include <string_view>
#include <vector>

namespace gcs::innards::hints
{
    /**
     * \brief lex's base assertion hint: just the owning constraint.
     *
     * Carried by the direct lex-pass inferences (the prefix-equality tightenings and
     * the contradiction when the order is violated). The explicit steps are emitted
     * by inline closures, so the base carries no data -- only the constraint
     * identity.
     *
     * \ingroup Innards
     */
    struct Lex
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "lex";
    };

    /**
     * \brief lex's "the order is forced unsatisfiable" hint, carried in a reified
     * verdict.
     *
     * Extends the base with the `unsat_scaffold` subhint and the emit context the
     * scaffold builder reads: the implicated reason, the two variable lists, the
     * compared prefix length, and the prefix-equal / decision-point aux-flag tables
     * (by shared_ptr), with the State by pointer (the verdict is consumed
     * synchronously while the constraint is live). Held for emit_justification only;
     * with no own hint_sexpr the hint takes the default identity-plus-subhint wire
     * form.
     *
     * \ingroup Innards
     */
    struct LexUnsatScaffold : Lex
    {
        static constexpr std::string_view subhint_name = "unsat_scaffold";
        const State * state;
        ReasonLiterals reason;
        std::vector<IntegerVariableID> first_vars, second_vars;
        std::size_t n;
        std::shared_ptr<std::vector<std::optional<ProofFlag>>> prefix_equal_flags;
        std::shared_ptr<std::vector<ProofFlag>> decision_at_flags;
    };

    auto emit_justification(ProofLogger & logger, const LexUnsatScaffold & scaffold, const ReasonLiterals & reason) -> void;
}

#endif
