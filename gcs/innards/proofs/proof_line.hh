#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_PROOF_LINE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_PROOF_LINE_HH

#include <gcs/innards/proofs/proof_line-fwd.hh>

#include <ostream>
#include <string>

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

    inline auto operator<<(std::ostream & s, const ProofLineNumber & n) -> std::ostream &
    {
        return s << n.number;
    }

    inline auto operator<<(std::ostream & s, const ProofLineLabel & l) -> std::ostream &
    {
        return s << "@" << l.label;
    }

    inline auto operator<<(std::ostream & s, const ProofLine & l) -> std::ostream &
    {
        return std::visit([&](const auto & l) -> std::ostream & { return s << l; }, l);
    }
}

#endif
