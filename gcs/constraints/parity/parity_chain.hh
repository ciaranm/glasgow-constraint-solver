#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PARITY_PARITY_CHAIN_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PARITY_PARITY_CHAIN_HH 1

#include <gcs/constraint_id.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/proof_model-fwd.hh>

#include <optional>
#include <string>

namespace gcs::innards
{
    /**
     * \brief Emit cake_pb_cp's accumulator-chain OPB encoding of "an odd number
     * of these literals is true", under the given constraint's identity.
     *
     * Shared by ParityOdd, which has one chain, and ParitySystem, which has one
     * per row: the point is that both entry points put the *same* rows in the
     * `.opb`, so the slack-form derivation that reads them back
     * (dev_docs/parity-system.md) is one piece of code rather than two.
     *
     * `row` disambiguates when there is more than one chain under one identity.
     * Left unset --- ParityOdd's case, and the only one cake ever sees --- the
     * flags are `x[id][k]` and the roles are `0ge`, `0le`, `<k>_0_0` and so on,
     * which is cake's naming exactly and must stay that way. Set, every flag
     * gains a leading index and every role a leading `r<row>_`, which keeps the
     * chains apart; nothing in cake's vocabulary corresponds to that, and
     * nothing needs to, because a constraint with several chains has no `.scp`
     * spelling to be checked against.
     *
     * \ingroup Innards
     */
    auto define_parity_chain(ProofModel & model, const ConstraintID & id, const std::optional<long long> & row, const Literals & lits) -> void;
}

#endif
