#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_TABULATION_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_TABULATION_HH

#include <gcs/constraints/extensional_utils.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <functional>
#include <optional>
#include <string>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief Under consistency::Auto, constraints tabulate when the enumeration
     * tree (the product of the enumerated variables' domain sizes) is no bigger
     * than this. The proof derivation emits a line per tree node, so this
     * bounds both the work and the proof size. The value is a guess, to be
     * benchmarked properly as a follow-up to issue #444.
     *
     * \ingroup Innards
     */
    constexpr long long default_tabulation_threshold = 100;

    /**
     * \brief Enumerate every assignment to vars that accept() approves, building
     * a table that can be handed to propagate_extensional() to achieve GAC.
     *
     * This is how a constraint can offer tabulated GAC without changing its OPB
     * encoding: the structural encoding stays whatever the constraint defines,
     * and the table is derived in-proof. With proof logging active, each
     * accepted tuple's selector literals are introduced via a pair of RED
     * lines, and every fully-explored subtree is closed with a RUP backtrack
     * line. Those backtrack lines are only verifiable if any complete
     * assignment that accept() rejects unit-propagates to a contradiction
     * against the owning constraint's structural OPB encoding; a caller must
     * make sure its encoding is strong enough for this before using tabulation.
     *
     * Returns nullopt if no assignment is accepted; the caller should then
     * infer FalseLiteral, which is RUP against the structural encoding for the
     * same reason as above. The proof derivation is skipped entirely in
     * assertion mode.
     *
     * The selector_name names the introduced selector literals in the proof
     * log, and comment is emitted before the derivation begins. Intended to be
     * called from an InitialiserPriority::Expensive initialiser; see
     * ReifiedLinearEquality's GAC path for the wiring.
     *
     * \ingroup Innards
     * \sa gcs::innards::propagate_extensional()
     */
    auto build_table_in_proof(const std::vector<IntegerVariableID> & vars, const std::function<auto(const std::vector<Integer> &)->bool> & accept,
        const std::string & selector_name, const std::string & comment, State & state, ProofLogger * const logger) -> std::optional<ExtensionalData>;
}

#endif
