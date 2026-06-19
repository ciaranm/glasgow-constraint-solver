
#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_ASSERTION_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_ASSERTION_HINTS_HH

#include <gcs/constraint_id.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>
#include <utility>
#include <variant>
#include <vector>
namespace gcs::innards
{

    /**
     * \brief The allowed names for annotated assertions.
     *
     * \ingroup Innards
     * \sa AssertionAnnotation
     */
    enum class AssertionHintName
    {
        None,
        AllDifferent,
        ReifiedEquals,
        Abs,
        ReifiedLinearEquality,
        InitialBound,
        BoundLink,
        Backtrack,
        SolxBlock,
        SoliImprove,
    };

    /**
     * \brief An assertion hint can be written as a string
     *
     * \ingroup Innards
     */
    inline auto operator<<(std::ostream & s, const AssertionHintName & hint_name) -> std::ostream &
    {
        switch (hint_name) {
        case AssertionHintName::None:
            return s << "None";
        case AssertionHintName::AllDifferent:
            return s << "AllDifferent";
        case AssertionHintName::ReifiedEquals:
            return s << "ReifiedEquals";
        case AssertionHintName::Abs:
            return s << "Abs";
        case AssertionHintName::ReifiedLinearEquality:
            return s << "ReifiedLinearEquality";
        case AssertionHintName::InitialBound:
            return s << "InitialBound";
        case AssertionHintName::BoundLink:
            return s << "BoundLink";
        case AssertionHintName::Backtrack:
            return s << "Backtrack";
        case AssertionHintName::SolxBlock:
            return s << "SolxBlock";
        case AssertionHintName::SoliImprove:
            return s << "SoliImprove";
        }
    }

    /**
     * \brief Kewords that can be used in assertion hint.
     *
     * \ingroup Innards
     * */
    enum class AssertionHintIdentifier
    {
        // Todo
    };

    /**
     * \brief The allowed field types that can appear in the
     * hints section of an annotated assertion.
     *
     * \ingroup Innards
     * \sa AssertionAnnotation
     */
    using AssertionHintField = std::variant<AssertionHintIdentifier, ProofLineLabel, ConstraintID, Integer, IntegerVariableID>;

    using AssertionHintRecord = std::variant<AssertionHintField, std::vector<AssertionHintField>, std::pair<AssertionHintField, std::vector<AssertionHintField>>>;

    /**
     * \brief An annotation for an annotated assertion step.
     *
     * \ingroup Innards
     */
    struct AssertionAnnotation
    {
        std::vector<ProofLineLabel> derivable_from = {};
        AssertionHintName hint_name = AssertionHintName::None;
        std::vector<AssertionHintRecord> hint_fields = {};
    };

    /**
     * \brief An assertion annotated can be written to an ostream.
     *
     * \ingroup Innards
     */
    inline auto operator<<(std::ostream & s, const AssertionAnnotation & annotation) -> std::ostream &
    {
        s << ":";
        for (const auto & id_or_label : annotation.derivable_from) {
            s << id_or_label << " ";
        }
        s << ":" << annotation.hint_name << ":";
        return s;
    }

} // namespace gcs::innards
#endif
