#include <gcs/constraints/innards/justify_not_in_range.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>

using namespace gcs;
using namespace gcs::innards;

auto gcs::innards::justify_not_in_range_across_equality(
    ProofLogger & logger,
    const ReasonFunction & reason,
    const SimpleIntegerVariableID & pruned,
    Integer lo,
    Integer hi,
    IntegerVariableID other,
    Integer other_lo,
    Integer other_hi) -> void
{
    // The range flag, reified to pruned's two order cuts (see need_invar).
    auto flag = logger.names_and_ids_tracker().need_invar(pruned, lo, hi);

    // ~flag \/ other >= other_lo. Negation is flag /\ other <= other_lo - 1; with
    // the equality linking pruned and other, that lower bound on pruned contradicts
    // the upper bound forced on other (Theorem 2.9), so the lemma is RUP.
    logger.emit_rup_proof_line_under_reason(reason,
        WPBSum{} + 1_i * ! flag + 1_i * (other >= other_lo) >= 1_i, ProofLevel::Temporary);

    // ~flag \/ other <= other_hi, written with the strict < form the encoding uses.
    logger.emit_rup_proof_line_under_reason(reason,
        WPBSum{} + 1_i * ! flag + 1_i * (other < other_hi + 1_i) >= 1_i, ProofLevel::Temporary);
}
