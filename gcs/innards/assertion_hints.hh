
#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_ASSERTION_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_ASSERTION_HINTS_HH

#include <gcs/constraint_id.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/integer.hh>

#include <optional>
#include <ostream>
#include <string>
#include <utility>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
using std::format;
#else
#include <fmt/core.h>
using fmt::format;
#endif

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
        return s;
    }

    /**
     * \brief Keywords that can be used in an assertion hint.
     *
     * \ingroup Innards
     */
    enum class AssertionHintIdentifier
    {
        constraint_id,
        // Todo
    };

    inline auto as_string(AssertionHintIdentifier identifier) -> std::string
    {
        switch (identifier) {
        case AssertionHintIdentifier::constraint_id:
            return "constraint_id";
        }
        return "";
    }

    /**
     * \brief Render a single hint field as an s-expression atom.
     *
     * \ingroup Innards
     */
    inline auto hint_sexpr(SExpr expr) -> SExpr
    {
        return expr;
    }

    inline auto hint_sexpr(AssertionHintIdentifier identifier) -> SExpr
    {
        return SExpr::atom(as_string(identifier));
    }

    inline auto hint_sexpr(const ProofLineLabel & label) -> SExpr
    {
        return SExpr::atom("@" + label.label);
    }

    inline auto hint_sexpr(const ConstraintID & id) -> SExpr
    {
        return SExpr::atom(as_string(id));
    }

    inline auto hint_sexpr(Integer value) -> SExpr
    {
        return SExpr::atom(value.to_string());
    }

    // NB: To put a variable in a hint, pass names_and_ids_tracker().s_expr_term_of(var)

    /**
     * \brief Build an s-expression hint from an arbitrary mix of fields and
     * nested hint lists. This is intended to cover every conceivable hint shape, even if
     * we're not in practice using the full generality at the moment.
     *
     * \ingroup Innards
     */
    template <typename... Ts_>
    inline auto hint_list(Ts_ &&... xs) -> SExpr
    {
        return SExpr::list({hint_sexpr(std::forward<Ts_>(xs))...});
    }

    /**
     * \brief An annotation for an annotated assertion step.
     *
     * \ingroup Innards
     */
    struct AssertionAnnotation
    {
        std::vector<ProofLineLabel> derivable_from = {};
        AssertionHintName hint_name = AssertionHintName::None;
        std::optional<SExpr> hint_fields = std::nullopt;
    };

    /**
     * \brief An assertion annotation can be written to an ostream.
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
        if (annotation.hint_fields)
            s << format("{}", *annotation.hint_fields);
        return s;
    }

} // namespace gcs::innards
#endif
