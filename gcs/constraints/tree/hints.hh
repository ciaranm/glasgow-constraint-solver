#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_TREE_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_TREE_HINTS_HH

#include <gcs/constraint_id.hh>

#include <string_view>

namespace gcs::innards::hints
{
    /**
     * \brief The tree family's assertion hint: just the owning constraint, no
     * subhint.
     *
     * Only DTree emits it, for its in-degree rows: Tree writes no rows of its own,
     * so its inferences come from its children. The originator pins down which
     * constraint.
     *
     * \ingroup Innards
     */
    struct Tree
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "tree";
    };
}

#endif
