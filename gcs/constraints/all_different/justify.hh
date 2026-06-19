#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_DIFFERENT_JUSTIFY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_DIFFERENT_JUSTIFY_HH

#include <gcs/constraint_id.hh>
#include <gcs/innards/proofs/names_and_ids_tracker-fwd.hh>
#include <gcs/innards/proofs/proof_logger.hh>
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
         */
        struct all_different_hall
        {
            std::vector<IntegerVariableID> hall_vars;
            std::vector<Integer> hall_vals;
            ConstraintID owner;
            static constexpr std::string_view justifier = "hall_set_or_violator";
        };

        [[nodiscard]] auto hint_sexpr(const all_different_hall & hall, NamesAndIDsTracker & names) -> SExpr;
    }
}

#endif
