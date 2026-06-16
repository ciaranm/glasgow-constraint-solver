#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>

#include <variant>

using namespace gcs;
using namespace gcs::innards;

// Check for proof-only range ("in") literals: introduce overlapping ranges in an
// adversarial order (cuts repeatedly inserted into the middle of the order chain,
// also splitting partition cells), then have VeriPB verify the key range-literal
// deductions by RUP. A width-1 request must come back as the eq atom itself, and
// out-of-bounds ranges are defined over their own cuts, with the bound axioms
// falsifying whatever lies outside.
auto main() -> int
{
    ProofOptions proof_options{"invar_test"};

    NamesAndIDsTracker tracker(proof_options);
    ProofModel model(proof_options, tracker);

    // One integer variable X, domain [0, 30].
    auto x = model.create_proof_only_integer_variable(0_i, 30_i, "x", IntegerVariableProofRepresentation::Bits);

    model.finalise();

    ProofLogger logger(proof_options, tracker);
    tracker.switch_from_model_to_proof(&logger);
    logger.start_proof(model);
    tracker.emit_delayed_proof_steps();

    // Adversarial introduction order: each range inserts cuts into the middle of the
    // existing chain and splits existing partition cells.
    auto r_10_20 = tracker.need_invar(x, 10_i, 20_i);
    auto r_10_17 = tracker.need_invar(x, 10_i, 17_i);
    auto r_13_20 = tracker.need_invar(x, 13_i, 20_i);
    auto r_13_17 = tracker.need_invar(x, 13_i, 17_i); // = [10,17] cap [13,20]

    // A width-1 interval IS the eq atom.
    auto r_15_15 = tracker.need_invar(x, 15_i, 15_i);
    if (r_15_15 != ProofLiteral{x == 15_i})
        return 1;

    // Idempotency: re-requesting an existing range returns the same literal.
    if (tracker.need_invar(x, 10_i, 17_i) != r_10_17)
        return 1;

    // Out-of-bounds ranges: defined over their own cuts. [25, 40] sticks out of the
    // upper bound; [35, 40] lies entirely outside.
    auto r_25_40 = tracker.need_invar(x, 25_i, 40_i);
    auto r_35_40 = tracker.need_invar(x, 35_i, 40_i);

    // negative covering: ~[10,17] AND ~[13,20] |- ~[10,20].
    logger.emit_rup_proof_line(WPBSum{} + 1_i * r_10_17 + 1_i * r_13_20 + 1_i * ! r_10_20 >= 1_i, ProofLevel::Current);

    // positive intersection: [10,17] AND [13,20] |- [13,17].
    logger.emit_rup_proof_line(WPBSum{} + 1_i * ! r_10_17 + 1_i * ! r_13_20 + 1_i * r_13_17 >= 1_i, ProofLevel::Current);

    // singleton containment: x = 15 |- [13,17].
    logger.emit_rup_proof_line(WPBSum{} + 1_i * (x != 15_i) + 1_i * r_13_17 >= 1_i, ProofLevel::Current);

    // the out-of-bounds part is dead by the bound axioms: [25,40] |- x <= 30.
    logger.emit_rup_proof_line(WPBSum{} + 1_i * ! r_25_40 + 1_i * ! (x >= 31_i) >= 1_i, ProofLevel::Current);

    // an entirely out-of-bounds range is just false.
    logger.emit_rup_proof_line(WPBSum{} + 1_i * ! r_35_40 >= 1_i, ProofLevel::Current);

    logger.conclude_none();
    tracker.finalise();

    return 0;
}
