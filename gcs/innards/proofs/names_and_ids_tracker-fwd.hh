#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_VARIABLE_CONSTRAINTS_TRACKER_FWD_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_VARIABLE_CONSTRAINTS_TRACKER_FWD_HH

#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <utility>
#include <vector>

namespace gcs::innards
{
    class NamesAndIDsTracker;

    /**
     * An `id == v` eq atom named by a proof line, and the set of them a line names.
     *
     * Lives in the -fwd header because PolBuilder needs the type to accumulate a union
     * across its operands, and cannot include the tracker proper (the tracker includes
     * PolBuilder).
     *
     * A vector rather than a set because these are tiny -- a handful of atoms per line at
     * most -- so a linear dedup beats any node-based container, and the whole point of the
     * structure is to stay cheap enough to carry per line.
     */
    using NamedEqAtom = std::pair<SimpleIntegerVariableID, Integer>;
    using NamedEqAtoms = std::vector<NamedEqAtom>;
}

#endif
