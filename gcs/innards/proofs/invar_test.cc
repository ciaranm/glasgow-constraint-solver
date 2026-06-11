#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>

#include <variant>

using namespace gcs;
using namespace gcs::innards;

// Check for proof-only range ("in") literals: introduce overlapping ranges in an
// adversarial order (cuts repeatedly inserted into the middle of the order chain,
// exercising additive Inv1 maintenance plus the partition splits of spec §3), then
// have VeriPB verify the key range-literal deductions by RUP. A width-1 request
// must come back as the eq atom itself, never a separate flag (witness W1's
// requirement, checked here at the API level).
auto main() -> int
{
    ProofOptions proof_options{"invar_test"};

    NamesAndIDsTracker tracker(proof_options);
    ProofModel model(proof_options, tracker);

    // One integer variable X, domain [0, 30]. All cuts below are interior.
    auto x = model.create_proof_only_integer_variable(0_i, 30_i, "x", IntegerVariableProofRepresentation::Bits);

    model.finalise();

    ProofLogger logger(proof_options, tracker);
    tracker.switch_from_model_to_proof(&logger);
    logger.start_proof(model);
    tracker.emit_delayed_proof_steps();

    // Adversarial introduction order: each range inserts cuts into the middle of the
    // existing chain and splits existing partition cells. cuts after each line:
    // {10,21} -> {10,18,21} -> {10,13,18,21} -> (reuse) -> {10,13,15,16,18,21}.
    auto r_10_20 = std::get<ProofFlag>(tracker.need_invar(x, 10_i, 20_i)); // [10,20]
    auto r_10_17 = std::get<ProofFlag>(tracker.need_invar(x, 10_i, 17_i)); // [10,17]
    auto r_13_20 = std::get<ProofFlag>(tracker.need_invar(x, 13_i, 20_i)); // [13,20]
    auto r_13_17 = std::get<ProofFlag>(tracker.need_invar(x, 13_i, 17_i)); // [13,17] = [10,17] cap [13,20]

    // A width-1 interval IS the eq atom (spec §2): no flag, the direct literal.
    auto r_15_15 = tracker.need_invar(x, 15_i, 15_i);
    if (r_15_15 != ProofLiteralOrFlag{ProofLiteral{x == 15_i}})
        return 1;

    // Idempotency: re-requesting an existing range returns the same flag, with no
    // second definition emitted.
    auto r_10_17_again = std::get<ProofFlag>(tracker.need_invar(x, 10_i, 17_i));
    if (r_10_17_again != r_10_17)
        return 1;

    // (a) negative covering (the Stage-0 headline): ~[10,17] AND ~[13,20] |- ~[10,20].
    logger.emit_rup_proof_line(WPBSum{} + 1_i * r_10_17 + 1_i * r_13_20 + 1_i * ! r_10_20 >= 1_i, ProofLevel::Current);

    // positive intersection: [10,17] AND [13,20] |- [13,17].
    logger.emit_rup_proof_line(WPBSum{} + 1_i * ! r_10_17 + 1_i * ! r_13_20 + 1_i * r_13_17 >= 1_i, ProofLevel::Current);

    // singleton containment: x = 15 |- [13,17].
    logger.emit_rup_proof_line(WPBSum{} + 1_i * (x != 15_i) + 1_i * r_13_17 >= 1_i, ProofLevel::Current);

    logger.conclude_none();
    tracker.finalise();

    return 0;
}
