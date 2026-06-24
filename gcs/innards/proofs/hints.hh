#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_HINTS_HH

#include <string_view>

namespace gcs::innards::hints
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

#endif
