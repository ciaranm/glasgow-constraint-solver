#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_HINTS_HH

#include <string_view>

namespace gcs::innards
{
    /**
     * \brief The empty hint: a bare justification carrying no assertion hint. This
     * is what JustifyUsingRUP{} / JustifyExplicitly{emit, then_rup} hold by default
     * (and hence what lives in the Justification variant).
     *
     * It lives here, the lightweight (\c string_view-only) hint-vocabulary leaf,
     * rather than next to the heavier s-expression machinery in assertion_hints.hh,
     * because it is the pervasive default: it is named by JustifyUsingRUP /
     * JustifyExplicitly and by lightweight propagator headers that must not pull in
     * the serialisation apparatus for a hint they never serialise.
     *
     * \ingroup Innards
     */
    struct NoHint
    {
    };

    /**
     * \brief The typed-assertion-hint customization surface.
     *
     * More than a bag of constants: this is where a typed hint and the two ADL
     * customization points it can opt into are co-located. A per-constraint hint
     * struct (in gcs/constraints/<foo>/hints.hh) is declared in this namespace so
     * that its
     *
     *   - \c hint_sexpr(hint, tracker) -- the wire-serialisation side, and
     *   - \c emit_justification(logger, hint, reason) -- the proof-emission side
     *
     * are found by argument-dependent lookup on the hint type (both are invoked
     * unqualified from infer_explicitly.hh). Co-locating the struct with its
     * \c hint_sexpr and \c emit_justification is the \c operator<< idiom: free
     * functions defined next to the type they customise.
     *
     * Defined here are the framework-owned hints (below) and the wire field-key
     * vocabulary (\c field); the generic s-expression machinery that consumes them
     * lives in assertion_hints.hh.
     *
     * \ingroup Innards
     */
    namespace hints
    {
        /**
         * \brief The s-expression field keys that make up a hint's wire form.
         *
         * A hint serialises as `((constraint_id <id>)(subhint <name>) ...)`; these are
         * the inner keys a justifier matches on. They live here, named, rather than as
         * `SExpr::atom("...")` literals scattered through the hint builders, so the wire
         * vocabulary the justifier consumes stays extractable in one place.
         *
         * \ingroup Innards
         */
        namespace field
        {
            inline constexpr std::string_view constraint_id = "constraint_id";
            inline constexpr std::string_view subhint = "subhint";
        }

        /**
         * \brief Assertion hints for the proof machinery itself, as opposed to a model
         * constraint's inferences.
         *
         * These name the framework-level assertions the prover emits around search and
         * solution handling. They are not owned by any model constraint, so -- unlike the
         * per-constraint hints -- they carry no \c originator and (for now) no fields, just
         * the coarse \c hint_name. If a justifier later needs the implicated variable, the
         * relevant struct gains a field and a \c hint_sexpr; until then they sit here so the
         * names live in the \c hints namespace rather than as scattered string literals.
         *
         * \ingroup Innards
         */
        struct InitialBound
        {
            static constexpr std::string_view hint_name = "initial_bound";
        };

        struct BoundLink
        {
            static constexpr std::string_view hint_name = "bound_link";
        };

        struct Backtrack
        {
            static constexpr std::string_view hint_name = "backtrack";
        };

        struct SolxBlock
        {
            static constexpr std::string_view hint_name = "solx_block";
        };

        struct SoliImprove
        {
            static constexpr std::string_view hint_name = "soli_improve";
        };
    }
}

#endif
