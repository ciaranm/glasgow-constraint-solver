#include <gcs/innards/proofs/lp_justification.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <map>
#include <vector>

using std::map;
using std::pair;
using std::vector;

auto gcs::innards::compute_lp_justification(
    const State & state,
    ProofLogger & logger,
    const WeightedPseudoBooleanLessEqual & inference,
    const vector<IntegerVariableID> & dom_vars,
    const vector<IntegerVariableID> & bound_vars,
    map<ProofLine, WeightedPseudoBooleanLessEqual> pb_constraints,
    bool compute_reason) -> pair<ExplicitJustificationFunction, Reason>
{
    ExplicitJustificationFunction just = [&](const Reason & reason) {
        logger.emit_under_reason(ProofRule::ASSERT, inference, ProofLevel::Current, reason);
    };

    vector<IntegerVariableID> all_vars{};
    all_vars.insert(all_vars.end(), dom_vars.begin(), dom_vars.end());
    all_vars.insert(all_vars.end(), bound_vars.begin(), bound_vars.end());

    auto reason = generic_reason(state, all_vars);
    return make_pair(just, reason);
}