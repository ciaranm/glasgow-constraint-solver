#ifndef GLASGOW_CONSTRAINT_SOLVER_CONSTRAINTS_ALL_DIFFERENT_ENCODING_HH
#define GLASGOW_CONSTRAINT_SOLVER_CONSTRAINTS_ALL_DIFFERENT_ENCODING_HH

#include <gcs/constraint.hh>
#include <gcs/innards/inference_tracker-fwd.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/innards/state.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <map>
#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace gcs
{
    namespace innards
    {
        // Emits the clique-of-not-equals encoding. Where the same variable
        // appears more than once in `vars`, the resulting pair-of-half-reified
        // constraints is jointly inconsistent — both polarities of the
        // selector are forced false. If any duplicate pair is found, the
        // return value carries one of the offending variables and its
        // selector flag, which the caller can cite from a justification that
        // derives contradiction explicitly (RUP alone cannot pick a polarity,
        // since both half-reifications are non-unit).
        auto define_clique_not_equals_encoding(ProofModel & model,
            const std::vector<IntegerVariableID> & vars) -> std::optional<std::pair<IntegerVariableID, ProofFlag>>;

        // Emits the AllDifferentExcept clique encoding. Where the same variable
        // appears more than once in `vars`, the resulting pair-of-half-reified
        // constraints implies that variable must take a value in `excluded`;
        // the returned map gives one of the per-pair selector flags for each
        // such duplicated variable, so callers can use it as the witness flag
        // in justifications that derive `var != v` for `v` not in `excluded`.
        auto define_clique_not_equals_except_encoding(ProofModel & model,
            const std::vector<IntegerVariableID> & vars,
            const std::vector<Integer> & excluded) -> std::map<IntegerVariableID, ProofFlag>;

        // Install a SimpleDefinition-priority contradiction initialiser that
        // proves the input was unsatisfiable because of a duplicate variable
        // in a clique-of-not-equals encoding. If proof logging is enabled and
        // a witness selector is supplied, the initialiser cites it
        // explicitly: it RUPs `selector` and `!selector` from the two
        // half-reifications the encoding emitted, then RUPs false. Otherwise
        // it just contradicts via plain RUP, which is enough when not
        // logging proofs.
        auto install_clique_duplicate_contradiction_initialiser(
            Propagators & propagators,
            std::optional<std::pair<IntegerVariableID, ProofFlag>> duplicate_witness) -> void;
    }
}

#endif
