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

    // Justify a bound on which_var_is_changing: the row plus every other term's
    // bound, which leaves that one variable's bits under the reason. Returns the
    // hints for the RUP of the bound that follows, which is the negation of
    // negated_conclusion: that line, the definition of negated_conclusion's
    // atom, and the boundary pin of any term whose bound the reason leaves out.
    // No hints when nothing was added to the row, or when negated_conclusion is
    // nullopt, which a gated row asks for: its gate is a reason literal, but
    // the row may be half-reified on a different literal the gate implies (a
    // stage citing cake's channel rows does), and crossing between the two is
    // the encoding's business, not something this can name.
    [[nodiscard]] auto justify_linear_bounds(ProofLogger & logger, const auto & coeff_vars, const LinearBounds & bounds,
        const SimpleIntegerVariableID & which_var_is_changing, bool use_second_constraint_for_equality,
        std::pair<std::optional<ProofLine>, std::optional<ProofLine>> proof_lines, const std::optional<IntegerVariableCondition> & negated_conclusion)
        -> RUPProofRule;

    // Justify inferring the negation of a gated linear stage's gate, when the
    // inequality is violated in bounds: materialise the sum of the
    // half-reified stage line and every term's bound, which reverse unit
    // propagation cannot combine on its own.
    auto justify_linear_contrapositive(ProofLogger & logger, const auto & coeff_vars, const LinearBounds & bounds, ProofLine proof_line) -> void;
}

#endif
