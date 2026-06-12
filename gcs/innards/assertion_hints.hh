
#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_ASSERTION_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_ASSERTION_HINTS_HH

#include <gcs/innards/proofs/proof_line.hh>
#include <vector>
namespace gcs::innards
{

    /**
     * \brief The allowed names for annotated assertions.
     *
     * \ingroup Innards
     * \sa AssertionAnnotation
     */
    enum AssertionHintName
    {
        None,
        AllDifferent
    };

    /**
     * \brief The allowed field types that can appear in the
     * hints section of an annotated assertion.
     *
     * \ingroup Innards
     * \sa AssertionAnnotation
     */
    enum AssertionHintField
    {
        // Hint field types will go here
    };

    /**
     * \brief An annotation for an annotated assertion step.
     *
     * \ingroup Innards
     */
    struct AssertionAnnotation
    {
        std::vector<ProofLineLabel> derivable_from = {};
        AssertionHintName hint_name = AssertionHintName::None;
        std::vector<AssertionHintField> hint_fields = {};
    };

} // namespace gcs::innards
#endif
