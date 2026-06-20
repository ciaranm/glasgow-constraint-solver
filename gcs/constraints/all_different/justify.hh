#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_DIFFERENT_JUSTIFY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_DIFFERENT_JUSTIFY_HH

#include <gcs/constraint_id.hh>
#include <gcs/innards/proofs/names_and_ids_tracker-fwd.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <map>
#include <string_view>
#include <vector>

namespace gcs::innards
{
    auto justify_all_different_hall_set_or_violator(
        ProofLogger &,
        const std::vector<IntegerVariableID> & all_variables,
        const std::vector<IntegerVariableID> & hall_variables,
        const std::vector<Integer> & hall_values,
        std::map<Integer, ProofLine> & constraint_numbers) -> void;

    // Typed assertion-hint witnesses live in gcs::innards::hints (reopened per
    // constraint); the namespace is the enumerable "interface the justifier
    // supports". Each struct owns its wire schema via a hint_sexpr overload and
    // its sub-rule keyword via a static constexpr `justifier`.
    namespace hints
    {
        /**
         * \brief Witness for the GAC all_different "Hall set or violator"
         * justification: the implicated variables, the values they collectively
         * saturate, and the owning constraint. Shared by the matching-too-small
         * contradiction and the SCC Hall-set deletion (same shape, different
         * owner and call site).
         *
         * The two trailing pointers are the per-constraint emit context (the full
         * variable scope and the constraint's mutable at-most-one line cache); they
         * are read only by emit_justification, not serialised by hint_sexpr. Both
         * point to data owned by the constraint, which outlives the whole search, so
         * a built witness is valid not just for eager emission but for storing and
         * replaying at backtrack time (the "fat witness" carrying emit context, with
         * hint_sexpr serialising only the clean subset).
         */
        struct AllDifferentHall
        {
            std::vector<IntegerVariableID> hall_vars;
            std::vector<Integer> hall_vals;
            ConstraintID owner;
            const std::vector<IntegerVariableID> * all_vars = nullptr;
            std::map<Integer, ProofLine> * value_am1_constraint_numbers = nullptr;
            static constexpr std::string_view justifier = "hall_set_or_violator";
            static constexpr std::string_view hint_name = "all_different";
        };

        [[nodiscard]] auto hint_sexpr(const AllDifferentHall & hall, NamesAndIDsTracker & names) -> SExpr;

        auto emit_justification(ProofLogger & logger, const AllDifferentHall & hall, const ReasonLiterals & reason) -> void;

        /**
         * \brief Witness for the trivial SCC deletion: a value is deleted because a
         * single other variable is forced to take it. The justification is plain
         * RUP (no explicit steps), so this witness has no emit_justification — it is
         * the pure-RUP capability tier, with only an assertion hint carrying the
         * owning constraint.
         */
        struct AllDifferentForcedValue
        {
            ConstraintID owner;
            static constexpr std::string_view hint_name = "all_different";
        };

        [[nodiscard]] auto hint_sexpr(const AllDifferentForcedValue & forced, NamesAndIDsTracker & names) -> SExpr;
    }
}

#endif
