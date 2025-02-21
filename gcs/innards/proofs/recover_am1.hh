#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_RECOVER_AM1_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_RECOVER_AM1_HH

#include <gcs/innards/proofs/proof_logger.hh>

#include <functional>
#include <vector>

namespace gcs::innards
{
    template <typename Literal_>
    [[nodiscard]] auto recover_am1(
        ProofLogger &,
        ProofLevel,
        const std::vector<Literal_> & atoms,
        const std::function<auto(const Literal_ &, const Literal_ &)->ProofLine> &) -> ProofLine;
}

#endif
