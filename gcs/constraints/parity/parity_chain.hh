#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PARITY_PARITY_CHAIN_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PARITY_PARITY_CHAIN_HH 1

#include <gcs/constraint_id.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_model-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>

#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief The rows and flags one accumulator chain put in the `.opb`, as the
     * slack-form derivation needs to cite them.
     *
     * Handed back by define_parity_chain, and reconstructible from a
     * ParityOdd's published ConstraintProofModelData, so that the derivation is
     * one piece of code whether the chain was emitted by ParitySystem or by a
     * separately posted constraint a presolver went looking for.
     *
     * \ingroup Innards
     */
    struct ParityChainRows
    {
        /// The four clauses of one step, `a_{k-1} XOR l_k XOR a_k = 0`, named
        /// for the (accumulator-in, literal) case each one rules out.
        struct Step
        {
            ProofLine c00, c11, c10, c01;
        };

        /// `a_0 .. a_n`: n + 1 of them for a chain over n literals.
        std::vector<ProofFlag> accumulators;
        std::vector<Step> steps;

        /// `a_0 <= 1`, `a_0 >= 1`, and `a_n <= 0`.
        ProofLine a0_le_1, a0_ge_1, an_le_0;
    };

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
    auto define_parity_chain(ProofModel & model, const ConstraintID & id, const std::optional<long long> & row, const Literals & lits)
        -> ParityChainRows;

    /**
     * \brief Derive the two pseudo-Boolean inequalities saying the chain's
     * literals sum to `1 + 2B`, and return them.
     *
     * Gocht and Nordstrom's (4.4a) and (4.4b) --- the form under which adding
     * two parity constraints together is one `pol` line. The accumulator chain
     * cannot state it directly, and a presolver could not add it to the `.opb`
     * even if it wanted to, so it is derived inside the proof at
     * ProofLevel::Top. See dev_docs/parity-system.md, "Deriving the slack row
     * from the accumulator chain", for the argument and for why each step needs
     * a `red` rather than a RUP.
     *
     * `flag_stem` names the fresh per-step variables and must be unique across
     * chains. Returns nullopt for a chain over no literals: there is no step to
     * telescope, `a_0` and `a_n` are the same flag, and nothing is needed ---
     * an empty odd row is a contradiction the chain's own three rows state.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto derive_parity_slack_rows(ProofLogger & logger, const ParityChainRows & chain, const Literals & lits,
        const std::string & flag_stem) -> std::optional<std::pair<ProofLine, ProofLine>>;
}

#endif
