#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PLUS_MINUS_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PLUS_MINUS_HINTS_HH

#include <gcs/constraint_id.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/reason.hh>

#include <optional>
#include <string_view>

namespace gcs::innards::hints
{
    /**
     * \brief plus's assertion hint for a bound push: the owning constraint and the
     * sum-definition line to start the cut from.
     *
     * plus has a single inference shape, so there is no subhint. emit_justification
     * starts the cut from pol_line and reads the two operand bounds positionally
     * from the reason -- a genuinely hint-driven emit -- but with no own hint_sexpr
     * the hint takes the default `(constraint_id <originator>)` wire form; pol_line
     * is held for emission, not serialised. pol_line is optional: with no sum line
     * (e.g. proofs without a model) emit does nothing and only the trailing RUP
     * stands.
     *
     * \ingroup Innards
     */
    struct Plus
    {
        ConstraintID originator;
        std::optional<ProofLine> pol_line;
        static constexpr std::string_view hint_name = "plus";
    };

    auto emit_justification(ProofLogger & logger, const Plus & plus, const ReasonLiterals & reason) -> void;

    /**
     * \brief minus's assertion hint for a bound push: the owning constraint and the
     * sum-definition line to start the cut from.
     *
     * The same shape as Plus (minus shares the bound-push proof pattern); a single
     * inference shape, so no subhint, and pol_line is held for emit_justification
     * rather than serialised.
     *
     * \ingroup Innards
     */
    struct Minus
    {
        ConstraintID originator;
        std::optional<ProofLine> pol_line;
        static constexpr std::string_view hint_name = "minus";
    };

    auto emit_justification(ProofLogger & logger, const Minus & minus, const ReasonLiterals & reason) -> void;
}

#endif
