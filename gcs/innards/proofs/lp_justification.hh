#ifndef GLASGOW_CONSTRAINT_SOLVER_LP_JUSTIFICATION_HH
#define GLASGOW_CONSTRAINT_SOLVER_LP_JUSTIFICATION_HH

#include <gcs/innards/justification.hh>
#include <gcs/innards/proofs/pseudo_boolean.hh>
#include <map>
#include <vector>

namespace gcs
{
    struct LPJustificationOptions
    {
        bool justify_everything_at_once = false;
        std::vector<IntegerVariableID> dom_vars = {};
        std::vector<IntegerVariableID> bound_vars = {};
    };
}
namespace gcs::innards
{
    [[nodiscard]] auto compute_lp_justification(
        const State & state,
        ProofLogger & logger,
        const WeightedPseudoBooleanLessEqual & inference,
        const LPJustificationOptions & lp_justification_options,
        const std::map<ProofLine, WeightedPseudoBooleanLessEqual> & pb_constraints) -> std::pair<ExplicitJustificationFunction, Reason>;
}
#endif // GLASGOW_CONSTRAINT_SOLVER_LP_JUSTIFICATION_HH
