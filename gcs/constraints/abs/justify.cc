#include <gcs/constraints/abs/justify.hh>

using namespace gcs;
using namespace gcs::innards;

auto gcs::innards::justify_abs_hole(
    ProofLogger & logger,
    const ReasonFunction & reason,
    IntegerVariableID v1,
    IntegerVariableID v2,
    Integer val) -> void
{
    // (v2 == val /\ v1 >= 0) -> v1 == val
    logger.emit_rup_proof_line_under_reason(reason,
        WeightedPseudoBooleanSum{} + 1_i * (v1 < 0_i) + 1_i * (v1 == val) + 1_i * (v2 != val) >= 1_i, ProofLevel::Temporary);

    // (v2 == val /\ v1 < 0) -> v1 == -val
    logger.emit_rup_proof_line_under_reason(reason,
        WeightedPseudoBooleanSum{} + 1_i * (v1 >= 0_i) + 1_i * (v1 != -val) + 1_i * (v2 != val) >= 1_i, ProofLevel::Temporary);

    // rest follows by RUP
}
