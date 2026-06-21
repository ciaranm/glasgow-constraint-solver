
#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_ASSERTION_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_ASSERTION_HINTS_HH

#include <gcs/constraint_id.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/integer.hh>

#include <optional>
#include <ostream>
#include <string>
#include <string_view>
#include <utility>
#include <vector>
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
     * \brief Render a single hint field as an s-expression atom.
     *
     * Field keys are plain s-expression atoms (e.g. \c SExpr::atom("hall_vars")),
     * not a fixed enum: the vocabulary of a hint's fields lives with that hint's
     * typed Data struct in \c gcs::innards::hints, not in one central list. The
     * \c hint_sexpr overloads below cover the leaf field values; per-hint Data
     * structs add their own \c hint_sexpr overload next to the constraint.
     *
     * \ingroup Innards
     */
    inline auto hint_sexpr(SExpr expr) -> SExpr
    {
        return expr;
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
     * \brief Build an s-expression list from a runtime range
     *
     * \ingroup Innards
     */
    template <typename Range_>
    inline auto hint_seq(const Range_ & xs) -> SExpr
    {
        std::vector<SExpr> children;
        for (const auto & x : xs)
            children.push_back(hint_sexpr(x));
        return SExpr::list(std::move(children));
    }

    /**
     * \brief The two ubiquitous hint fields, as named constructors.
     *
     * Almost every typed hint carries the owning constraint id, and the multi-shape
     * ones add a per-shape \c justifier keyword. These spell those two
     * `(constraint_id <id>)` / `(justifier <name>)` field pairs once, so each
     * witness's \c hint_sexpr names them rather than respelling the atom pairs.
     *
     * \ingroup Innards
     */
    inline auto hint_constraint_id(const ConstraintID & owner) -> SExpr
    {
        return hint_list(SExpr::atom("constraint_id"), owner);
    }

    inline auto hint_justifier(std::string_view justifier) -> SExpr
    {
        return hint_list(SExpr::atom("justifier"), SExpr::atom(std::string{justifier}));
    }

    /**
     * \brief An annotation for an annotated assertion step.
     *
     * \ingroup Innards
     */
    struct AssertionAnnotation
    {
        std::vector<ProofLineLabel> derivable_from = {};
        // A coarse, model-level constraint-type name (e.g. "all_different",
        // "abs"), carried in the second annotation field for vanilla-VeriPB
        // statistics. The fine, per-justification-shape discriminator (the
        // "justifier" keyword) lives in hint_fields, set by the typed Data
        // struct. A string literal, so this stays allocation-free.
        std::string_view hint_name = "";
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
