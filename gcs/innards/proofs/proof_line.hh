#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_PROOF_LINE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_PROOF_LINE_HH

#include <gcs/innards/proofs/proof_line-fwd.hh>

#include <ostream>
#include <string>
#include <variant>

namespace gcs::innards
{
    struct ProofLineNumber
    {
        long long number;

        [[nodiscard]] auto operator<=>(const ProofLineNumber &) const = default;
    };

    struct ProofLineLabel
    {
        std::string label;

        [[nodiscard]] auto operator<=>(const ProofLineLabel &) const = default;
    };

    // A label is a name (e.g. `@c[_1][le]`), count-robust, so streaming it as a
    // constraint *definition* prefix is fine. There is deliberately no ostream
    // operator for ProofLineNumber / ProofLine: a numeric line is a *reference*,
    // and references must be emitted relative to the current line via
    // relative_proof_line() (see below) so they survive the solver's OPB and
    // cake_pb_cp's re-derived OPB differing in constraint count. Streaming a bare
    // number would silently emit an absolute reference and break workflow-2.
    inline auto operator<<(std::ostream & s, const ProofLineLabel & l) -> std::ostream &
    {
        return s << "@" << l.label;
    }

    /**
     * Render a proof-line reference as VeriPB's *relative* (negative) constraint
     * index, counting back from the most-recently emitted constraint
     * `current_max`. A positive `ProofLineNumber` is treated as an absolute id
     * and converted to `n - current_max - 1` (so the most recent line, `n ==
     * current_max`, becomes `-1`); a non-positive number is already relative (or
     * the "no line" sentinel `0`) and passes through unchanged; a label passes
     * through as `@label` (name references are count-robust by construction).
     *
     * Relative references survive the solver's OPB and cake_pb_cp's re-derived
     * OPB differing in constraint count (e.g. cake emitting two bound lines for a
     * binary variable where the solver emits one): the gap between any two
     * derived constraints is the same on both sides, so the offset is too.
     */
    [[nodiscard]] inline auto relative_proof_line(const ProofLine & l, long long current_max) -> std::string
    {
        if (auto n = std::get_if<ProofLineNumber>(&l)) {
            if (n->number > 0)
                return std::to_string(n->number - current_max - 1);
            else
                return std::to_string(n->number);
        }
        else
            return "@" + std::get<ProofLineLabel>(l).label;
    }
}

#endif
