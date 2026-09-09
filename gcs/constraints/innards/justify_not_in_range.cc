#include <gcs/constraints/innards/justify_not_in_range.hh>

using namespace gcs;
using namespace gcs::innards;

using std::move;
using std::optional;

auto gcs::innards::justify_not_in_range_across_equality(ProofLogger & logger, const ReasonLiterals & reason, const SimpleIntegerVariableID & pruned,
    Integer lo, Integer hi, IntegerVariableID other, Integer other_lo, Integer other_hi, const optional<ProofFlag> & under) -> void
{
    // pruned >= lo -> other >= other_lo. Negation is pruned >= lo AND
    // other <= other_lo - 1; with the equality linking pruned and other these
    // are the opposing bounds of the Theorem 2.9 configuration, so the lemma
    // is RUP. No flag appears unless the caller's link needs one: see the
    // header for why the ge-layer factoring is preferred, for the same-sign
    // orientation requirement, and for what a guarded link changes.
    auto lower = WPBSum{} + 1_i * (pruned < lo) + 1_i * (other >= other_lo);
    if (under)
        lower += 1_i * ! *under;
    logger.emit_rup_proof_line_under_reason(reason, move(lower) >= 1_i, ProofLevel::Temporary);

    // other >= other_hi + 1 -> pruned >= hi + 1, written with the strict <
    // form the encoding uses. Same Theorem 2.9 shape, upper side.
    auto upper = WPBSum{} + 1_i * (other < other_hi + 1_i) + 1_i * (pruned >= hi + 1_i);
    if (under)
        upper += 1_i * ! *under;
    logger.emit_rup_proof_line_under_reason(reason, move(upper) >= 1_i, ProofLevel::Temporary);
}
