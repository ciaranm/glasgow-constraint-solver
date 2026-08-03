#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_VARIABLE_CONSTRAINTS_TRACKER_FWD_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_VARIABLE_CONSTRAINTS_TRACKER_FWD_HH

#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <utility>
#include <vector>

namespace gcs::innards
{
    class NamesAndIDsTracker;

    enum class EqualsOrGreaterEqual
    {
        Equals,
        GreaterEqual
    };

    /**
     * A deletable order-encoding atom named by a proof line: `id == v` or `id >= v`.
     *
     * Lives in the -fwd header because PolBuilder needs the type to accumulate a union
     * across its operands, and cannot include the tracker proper (the tracker includes
     * PolBuilder).
     */
    struct NamedAtom
    {
        SimpleIntegerVariableID id;
        Integer value;
        EqualsOrGreaterEqual kind;

        [[nodiscard]] auto operator==(const NamedAtom &) const -> bool = default;
    };

    /**
     * The set of atoms one line names.
     *
     * A vector rather than a set because these are tiny -- a handful of atoms per line at
     * most -- so a linear dedup beats any node-based container, and the whole point of the
     * structure is to stay cheap enough to carry per line.
     */
    using NamedAtoms = std::vector<NamedAtom>;
}

#endif
