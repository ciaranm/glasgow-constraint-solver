#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_JUSTIFY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LINEAR_JUSTIFY_HH

#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <gch/small_vector.hpp>

#include <optional>
#include <utility>

namespace gcs::innards
{
    // The per-variable (lower, upper) snapshot a linear propagation works over.
    // Rebuilt on every firing, so it keeps the common small-arity case in inline
    // storage to stay off the heap; wider constraints spill to the heap as usual.
    using LinearBounds = gch::small_vector<std::pair<Integer, Integer>, 8>;

    auto justify_linear_bounds(ProofLogger & logger, const auto & coeff_vars, const LinearBounds & bounds,
        const SimpleIntegerVariableID & which_var_is_changing, bool use_second_constraint_for_equality,
        std::pair<std::optional<ProofLine>, std::optional<ProofLine>> proof_lines) -> void;

    // Justify inferring the negation of a gated linear stage's gate, when the
    // inequality is violated in bounds: materialise the sum of the
    // half-reified stage line and every term's bound, which reverse unit
    // propagation cannot combine on its own.
    auto justify_linear_contrapositive(ProofLogger & logger, const auto & coeff_vars, const LinearBounds & bounds, ProofLine proof_line) -> void;
}

#endif
