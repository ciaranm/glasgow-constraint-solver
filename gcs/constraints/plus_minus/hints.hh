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
     * Its bounds-consistency propagator has a single inference shape, so there
     * is no subhint (the GAC arm's range removals carry PlusNotInRange, below,
     * instead). emit_justification
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
        // Defaulted so that a caller which has no sum line to offer -- the
        // tabulated path builds its hints as Plus{owner} -- is not a
        // -Wmissing-field-initializers site.
        std::optional<ProofLine> pol_line = std::nullopt;
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
        // Defaulted for the same reason as Plus::pol_line, above.
        std::optional<ProofLine> pol_line = std::nullopt;
        static constexpr std::string_view hint_name = "minus";
    };

    auto emit_justification(ProofLogger & logger, const Minus & minus, const ReasonLiterals & reason) -> void;

    /**
     * \brief plus's "not in this interval" hint, for the consistency::GAC arm.
     *
     * The GAC arm removes a run of values that no pair of operand values sums
     * to, and a range conclusion over a three-variable sum is not RUP: it takes
     * one or two bound lemmas per interval of the operand it walks, each a `pol`
     * over one half of the sum line (see plus_minus/gac.cc). That makes it a
     * multi-line derivation, which the bare Plus hint -- one `pol` whose two
     * operand bounds are read positionally from the reason -- does not describe.
     *
     * Nothing beyond the subhint: the emission is a lambda at the call site, and
     * an external justifier gets the run from the asserted literal and the other
     * two variables' domains from the reason, which states each of them exactly.
     *
     * \ingroup Innards
     */
    struct PlusNotInRange
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "plus";
        static constexpr std::string_view subhint_name = "not_in_range";
    };

    /**
     * \brief minus's "not in this interval" hint, for the consistency::GAC arm;
     * the same shape as PlusNotInRange.
     *
     * \ingroup Innards
     */
    struct MinusNotInRange
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "minus";
        static constexpr std::string_view subhint_name = "not_in_range";
    };
}

#endif
