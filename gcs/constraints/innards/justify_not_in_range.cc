#include <gcs/constraints/innards/justify_not_in_range.hh>

using namespace gcs;
using namespace gcs::innards;

using std::move;
using std::optional;

auto gcs::innards::justify_not_in_range_across_equality(ProofLogger & logger, const ReasonLiterals & reason, const IntegerVariableID & pruned,
    Integer lo, Integer hi, IntegerVariableID other, Integer other_lo, Integer other_hi, const optional<ProofFlag> & under) -> void
{
    auto lower = WPBSum{} + 1_i * (pruned < lo) + 1_i * (other >= other_lo);
    if (under)
        lower += 1_i * ! *under;
    logger.emit_rup_proof_line_under_reason(reason, move(lower) >= 1_i, ProofLevel::Temporary);

    auto upper = WPBSum{} + 1_i * (other < other_hi + 1_i) + 1_i * (pruned >= hi + 1_i);
    if (under)
        upper += 1_i * ! *under;
    logger.emit_rup_proof_line_under_reason(reason, move(upper) >= 1_i, ProofLevel::Temporary);
}
