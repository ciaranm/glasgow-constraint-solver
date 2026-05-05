#ifndef GLASGOW_CONSTRAINT_SOLVER_CONSTRAINTS_ALL_DIFFERENT_ENCODING_HH
#define GLASGOW_CONSTRAINT_SOLVER_CONSTRAINTS_ALL_DIFFERENT_ENCODING_HH

#include <gcs/constraint.hh>
#include <gcs/innards/inference_tracker-fwd.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/state.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <map>
#include <vector>

namespace gcs
{
    namespace innards
    {
        auto define_clique_not_equals_encoding(ProofModel & model,
            const std::vector<IntegerVariableID> & vars) -> void;

        // Emits the AllDifferentExcept clique encoding. Where the same variable
        // appears more than once in `vars`, the resulting pair-of-half-reified
        // constraints implies that variable must take a value in `excluded`;
        // the returned map gives one of the per-pair selector flags for each
        // such duplicated variable, so callers can use it as the witness flag
        // in justifications that derive `var != v` for `v` not in `excluded`.
        auto define_clique_not_equals_except_encoding(ProofModel & model,
            const std::vector<IntegerVariableID> & vars,
            const std::vector<Integer> & excluded) -> std::map<IntegerVariableID, ProofFlag>;
    }
}

#endif
