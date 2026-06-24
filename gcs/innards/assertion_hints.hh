
#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_ASSERTION_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_ASSERTION_HINTS_HH

#include <gcs/constraint_id.hh>
#include <gcs/innards/proofs/hints.hh>
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
    class NamesAndIDsTracker;

    /**
     * \brief Render a single hint field's value as an s-expression atom.
     *
     * These \c hint_sexpr overloads cover the leaf field *values* (a label, a
     * constraint id, an integer). The common field *keys* are named in
     * \c hints::field (gcs/innards/proofs/hints.hh) so the wire vocabulary the
     * justifier matches on stays extractable; a per-hint \c hint_sexpr that
     * serialises extra data names its own keys next to the constraint.
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
     * \brief The owning-constraint-id field, as a named constructor.
     *
     * Almost every typed hint carries the owning constraint id; the default
     * \c hint_sexpr (in the \c hints namespace below) spells the
     * `(constraint_id <id>)` field once so each hint names it rather than
     * respelling the atom pair. The per-shape `(subhint <name>)` field has its own
     * spelling, \c hint_subhint.
     *
     * \ingroup Innards
     */
    inline auto hint_constraint_id(const ConstraintID & owner) -> SExpr
    {
        return hint_list(SExpr::atom(std::string{hints::field::constraint_id}), owner);
    }

    namespace hints
    {
        /**
         * \brief The `(subhint <name>)` field: the per-shape discriminator for a
         * constraint family whose internal proof writer distinguishes more than one
         * inference shape (e.g. all_different's "hall" vs "forced_value"). Spelled
         * once here so every derived hint struct names it the same way.
         *
         * \ingroup Innards
         */
        inline auto hint_subhint(std::string_view name) -> SExpr
        {
            return hint_list(SExpr::atom(std::string{field::subhint}), SExpr::atom(std::string{name}));
        }

        /**
         * \brief The default wire form for a typed assertion hint: the identity
         * only.
         *
         * Emits just `(constraint_id <originator>)`, plus `(subhint <name>)` when the
         * hint struct names one. It carries NO operand data: everything an external
         * justifier needs that is re-derivable from the asserted literal, the reason
         * and the definition lines stays off the wire (the internal proof writer
         * holds it for its own emission). A constraint opts into serialising more by
         * defining its own `hint_sexpr` overload next to its hint struct; that is the
         * single place where the external data is allowed to be a (possibly strict)
         * subset of the internal data.
         *
         * \ingroup Innards
         */
        template <typename Hint_>
            requires requires(const Hint_ & h) { h.originator; }
        auto hint_sexpr(const Hint_ & h, NamesAndIDsTracker &) -> SExpr
        {
            if constexpr (requires { Hint_::subhint_name; })
                return hint_list(hint_constraint_id(h.originator), hint_subhint(Hint_::subhint_name));
            else
                return hint_list(hint_constraint_id(h.originator));
        }
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
        // "abs"): the first port-of-call for justification dispatch. A justifier
        // picks its function by constraint family from this name, and only reads
        // the structured hint_fields below -- the per-shape "subhint", plus any
        // data -- when the family alone doesn't determine the function. It is also
        // what a vanilla VeriPB run can aggregate for statistics. A string literal,
        // so this stays allocation-free.
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
