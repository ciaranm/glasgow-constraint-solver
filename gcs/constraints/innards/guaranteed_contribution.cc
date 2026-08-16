#include <gcs/constraints/innards/guaranteed_contribution.hh>
#include <gcs/innards/power.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>

#include <optional>
#include <utility>
#include <variant>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::move;
using std::optional;
using std::size_t;
using std::vector;

auto gcs::innards::guaranteed_contribution_row(ProofLogger & logger, const ReasonLiterals * const reason, const vector<ProofFlag> & contribution_bits,
    const ProofFlag & active, const SimpleIntegerVariableID & height, Integer bound, ProofLine contribution_ge_row, ProofLevel level) -> ProofLine
{
    auto & tracker = logger.names_and_ids_tracker();

    // The atom's definition supplies the bits; the unit saying the atom holds
    // is what makes the row unconditional. Where the bound is the height's
    // declared one, need_gevar has already pinned that as a persistent
    // top-of-proof line, so cite it rather than emit the same unit again per
    // row. Anywhere else the fact is still permanent for the subtree, but
    // nothing has written it down: a unit RUP does, under the reason where the
    // caller gave one --- and a caller that did not is claiming the bound is a
    // root fact, which is the case a proof-logged tightening closes against.
    auto at_least = height >= bound;
    auto definition = tracker.need_pol_item_defining_literal(at_least);
    auto holds = tracker.boundary_pin_line(height, bound);
    if (! holds)
        holds = reason ? logger.emit_rup_proof_line_under_reason(*reason, WPBSum{} + 1_i * at_least >= 1_i, level)
                       : logger.emit_rup_proof_line(WPBSum{} + 1_i * at_least >= 1_i, level);

    optional<vector<ProofLine>> hints;
    if (auto line = std::get_if<ProofLine>(&definition))
        hints = vector<ProofLine>{contribution_ge_row, *line, *holds};

    WPBSum guaranteed;
    for (size_t k = 0; k < contribution_bits.size(); ++k)
        guaranteed += power2(Integer(static_cast<long long>(k))) * contribution_bits[k];
    guaranteed += bound * ! active;

    // Under the reason where there is one, and not merely to record what the
    // line depends on: the unit saying the height reaches the bound is itself
    // reason-backed whenever the bound is not the declared one, so it is a
    // *clause* carrying the reason's negations rather than a unit. A goal
    // stated without the reason leaves those literals unassigned, the clause
    // does not propagate, and the hint is worth nothing --- which is a rejected
    // proof and not a slow one.
    return reason ? logger.emit_under_reason(RUPProofRule{hints}, move(guaranteed) >= bound, level, *reason)
                  : logger.emit(RUPProofRule{hints}, move(guaranteed) >= bound, level);
}
