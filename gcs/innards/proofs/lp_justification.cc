#include <gcs/innards/proofs/lp_justification.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <map>
#include <vector>

using std::map;
using std::vector;

auto gcs::innards::compute_lp_justification(
    const State & state,
    ProofLogger & logger,
    const WeightedPseudoBooleanLessEqual & inference,
    const vector<IntegerVariableID> & dom_vars,
    const vector<IntegerVariableID> & bound_vars,
    map<ProofLine, WeightedPseudoBooleanLessEqual> pb_constraints,
    const bool use_reason) -> ExplicitJustificationFunction
{
    ExplicitJustificationFunction just = [&logger](const Reason & reason) {
        
    };
    return just;
}