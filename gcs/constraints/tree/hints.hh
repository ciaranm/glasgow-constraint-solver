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
     * Both spellings use it, as Reachable and DReachable share theirs: the
     * originator pins down which constraint, and the `.scp` says whether that
     * one is a `tree` or a `dtree`.
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
