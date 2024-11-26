#ifndef GLASGOW_CONSTRAINT_SOLVER_LP_JUSTIFICATION_HH
#define GLASGOW_CONSTRAINT_SOLVER_LP_JUSTIFICATION_HH

#include <gcs/innards/justification.hh>
#include <gcs/innards/proofs/pseudo_boolean.hh>
#include <map>
#include <vector>

namespace gcs::innards
{
    [[nodiscard]] auto compute_lp_justification(
        const State & state,
        ProofLogger & logger,
        const WeightedPseudoBooleanLessEqual & inference,
        const std::vector<IntegerVariableID> & dom_vars,
        const std::vector<IntegerVariableID> & bound_vars,
        std::map<ProofLine, WeightedPseudoBooleanLessEqual> pb_constraints,
        const bool use_reason = false) -> ExplicitJustificationFunction;
}
#endif // GLASGOW_CONSTRAINT_SOLVER_LP_JUSTIFICATION_HH
