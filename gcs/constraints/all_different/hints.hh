#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_DIFFERENT_HINTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_DIFFERENT_HINTS_HH

#include <gcs/constraint_id.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/reason.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <map>
#include <string_view>
#include <vector>

namespace gcs::innards::hints
{
    /**
     * \brief all_different's base assertion hint: just the owning constraint.
     *
     * Used directly for the trivial SCC deletions, where a value is removed
     * because a single other variable is forced to take it -- a pure-RUP
     * inference with nothing to disambiguate, so it carries no subhint and takes
     * the default `(constraint_id <originator>)` wire form.
     *
     * \ingroup Innards
     */
    struct AllDifferent
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "all_different";
    };

    /**
     * \brief all_different's GAC "Hall set or violator" hint.
     *
     * Extends the base with the per-shape `hall` subhint and the emit context the
     * internal proof writer needs: the implicated Hall variables and values, the
     * full variable scope, and the constraint's mutable at-most-one line cache.
     * Those pointers reference constraint-owned data that outlives the search, so
     * a built hint is valid both for eager emission and for replay at backtrack
     * time. The data is held for emit_justification only; with no own hint_sexpr
     * the hint takes the default identity-plus-subhint wire form
     * (`(constraint_id <originator>)(subhint hall)`), keeping the Hall set off the
     * wire unless an external justifier opts into serialising it.
     *
     * \ingroup Innards
     */
    struct AllDifferentHall : AllDifferent
    {
        static constexpr std::string_view subhint_name = "hall";
        std::vector<IntegerVariableID> hall_vars;
        std::vector<Integer> hall_vals;
        const std::vector<IntegerVariableID> * all_vars = nullptr;
        std::map<Integer, ProofLine> * value_am1_constraint_numbers = nullptr;
    };

    auto emit_justification(ProofLogger & logger, const AllDifferentHall & hall, const ReasonLiterals & reason) -> void;

    /**
     * \brief all_different_except's assertion hint: just the owning constraint.
     *
     * AllDifferentExcept is a distinct constraint (not a shape of AllDifferent), so
     * it gets its own base hint rather than reusing AllDifferent's: its name lets the
     * justifier dispatch on the right family. Carried by the duplicate-forcing
     * prunings and the clique-duplicate contradiction, both RUP-derivable, so no
     * subhint and the default `(constraint_id <originator>)` wire form.
     *
     * \ingroup Innards
     */
    struct AllDifferentExcept
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "all_different_except";
    };
}

#endif
