#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>

using namespace gcs;
using namespace gcs::innards;

// ProofLogger::introduce_bits_of introduces a proof-only `end` that has no OPB
// encoding (create_proof_only_integer_variable_in_proof) as the bit-decomposition
// of the linear form s + l, via Wietze Koops's 2m redundancy steps. VeriPB checks
// the redundancy of every step, so a clean run is the verification. This ports the
// standalone prototype: s, l in [0, 3]; end in [0, 6] (3 bits, since 2^3 > 3 + 3).
auto main() -> int
{
    ProofOptions proof_options{"introduce_bits_test"};

    NamesAndIDsTracker tracker(proof_options);
    ProofModel model(proof_options, tracker);

    // s and l are ordinary bits-encoded variables (their encoding IS in the OPB).
    auto s = model.create_proof_only_integer_variable(0_i, 3_i, "s", IntegerVariableProofRepresentation::Bits);
    auto l = model.create_proof_only_integer_variable(0_i, 3_i, "l", IntegerVariableProofRepresentation::Bits);
    // end is registered but not encoded in the OPB; its meaning is introduced in
    // the proof below as end = s + l.
    auto end = model.create_proof_only_integer_variable_in_proof(0_i, 6_i, "end");

    // Signed targets (issue #553): when the form's lower bound is negative the
    // target carries a sign bit and the construction runs shifted by 2^S.
    // The issue's own shape: s2 + l2 reaches -1.
    auto s2 = model.create_proof_only_integer_variable(-1_i, 2_i, "s2", IntegerVariableProofRepresentation::Bits);
    auto l2 = model.create_proof_only_integer_variable(0_i, 2_i, "l2", IntegerVariableProofRepresentation::Bits);
    auto end2 = model.create_proof_only_integer_variable_in_proof(-1_i, 4_i, "end2");
    // Operand sign reaching below the target's: s3's encoding spans [-16, 15]
    // but end3's only [-8, 7], so the top le redundancy goal (s3 + l3 >= -8)
    // closes only through propagation of s3's lower-bound row, not by slack.
    auto s3 = model.create_proof_only_integer_variable(-10_i, 0_i, "s3", IntegerVariableProofRepresentation::Bits);
    auto l3 = model.create_proof_only_integer_variable(2_i, 3_i, "l3", IntegerVariableProofRepresentation::Bits);
    auto end3 = model.create_proof_only_integer_variable_in_proof(-8_i, 3_i, "end3");
    // Sign-only target (no value bits) over a zero-width operand ({0}, the
    // empty sum).
    auto s4 = model.create_proof_only_integer_variable(-1_i, 0_i, "s4", IntegerVariableProofRepresentation::Bits);
    auto l4 = model.create_proof_only_integer_variable(0_i, 0_i, "l4", IntegerVariableProofRepresentation::Bits);
    auto end4 = model.create_proof_only_integer_variable_in_proof(-1_i, 0_i, "end4");
    // A negative form coefficient: end5 = s5 - l5 spans [-3, 3].
    auto s5 = model.create_proof_only_integer_variable(0_i, 3_i, "s5", IntegerVariableProofRepresentation::Bits);
    auto l5 = model.create_proof_only_integer_variable(0_i, 3_i, "l5", IntegerVariableProofRepresentation::Bits);
    auto end5 = model.create_proof_only_integer_variable_in_proof(-3_i, 3_i, "end5");

    // Shapes whose top-step redundancy goals unit propagation alone cannot
    // close (they stall at a propagation fixpoint), so they check the derived
    // form-bound pol lines specifically.
    // s6's encoding spans [-32, 31], far overhanging end6's [-8, 7]: the
    // issue #553 review's counterexample.
    auto s6 = model.create_proof_only_integer_variable(-17_i, -16_i, "s6", IntegerVariableProofRepresentation::Bits);
    auto l6 = model.create_proof_only_integer_variable(9_i, 16_i, "l6", IntegerVariableProofRepresentation::Bits);
    auto end6 = model.create_proof_only_integer_variable_in_proof(-8_i, 0_i, "end6");
    // Three signed operands, unit coefficients.
    auto s7a = model.create_proof_only_integer_variable(-5_i, 0_i, "s7a", IntegerVariableProofRepresentation::Bits);
    auto s7b = model.create_proof_only_integer_variable(-5_i, 0_i, "s7b", IntegerVariableProofRepresentation::Bits);
    auto s7c = model.create_proof_only_integer_variable(-5_i, 0_i, "s7c", IntegerVariableProofRepresentation::Bits);
    auto end7 = model.create_proof_only_integer_variable_in_proof(-15_i, 0_i, "end7");
    // Three negated non-negative operands.
    auto x8a = model.create_proof_only_integer_variable(0_i, 5_i, "x8a", IntegerVariableProofRepresentation::Bits);
    auto x8b = model.create_proof_only_integer_variable(0_i, 5_i, "x8b", IntegerVariableProofRepresentation::Bits);
    auto x8c = model.create_proof_only_integer_variable(0_i, 5_i, "x8c", IntegerVariableProofRepresentation::Bits);
    auto end8 = model.create_proof_only_integer_variable_in_proof(-15_i, 0_i, "end8");
    // A ge-side stall: the operands' encodings reach 25 but end9 tops out
    // at 24, over a signed target.
    auto s9 = model.create_proof_only_integer_variable(-1_i, 0_i, "s9", IntegerVariableProofRepresentation::Bits);
    auto x9a = model.create_proof_only_integer_variable(0_i, 8_i, "x9a", IntegerVariableProofRepresentation::Bits);
    auto x9b = model.create_proof_only_integer_variable(0_i, 8_i, "x9b", IntegerVariableProofRepresentation::Bits);
    auto x9c = model.create_proof_only_integer_variable(0_i, 8_i, "x9c", IntegerVariableProofRepresentation::Bits);
    auto end9 = model.create_proof_only_integer_variable_in_proof(-1_i, 24_i, "end9");
    // The unsigned analogue of the stall (pre-existing, not issue #553).
    auto x10a = model.create_proof_only_integer_variable(0_i, 8_i, "x10a", IntegerVariableProofRepresentation::Bits);
    auto x10b = model.create_proof_only_integer_variable(0_i, 8_i, "x10b", IntegerVariableProofRepresentation::Bits);
    auto x10c = model.create_proof_only_integer_variable(0_i, 8_i, "x10c", IntegerVariableProofRepresentation::Bits);
    auto end10 = model.create_proof_only_integer_variable_in_proof(0_i, 24_i, "end10");

    model.finalise();

    ProofLogger logger(proof_options, tracker);
    tracker.switch_from_model_to_proof(&logger);
    logger.start_proof(model);
    tracker.emit_delayed_proof_steps();

    // The 2m reds. The returned pair is BinEnc(end) >= s + l / <= s + l; we don't
    // need to reference them here --- VeriPB has already verified each step.
    [[maybe_unused]] auto [ge, le] = logger.introduce_bits_of(WPBSum{} + 1_i * s + 1_i * l, end, ProofLevel::Top);
    [[maybe_unused]] auto [ge2, le2] = logger.introduce_bits_of(WPBSum{} + 1_i * s2 + 1_i * l2, end2, ProofLevel::Top);
    [[maybe_unused]] auto [ge3, le3] = logger.introduce_bits_of(WPBSum{} + 1_i * s3 + 1_i * l3, end3, ProofLevel::Top);
    [[maybe_unused]] auto [ge4, le4] = logger.introduce_bits_of(WPBSum{} + 1_i * s4 + 1_i * l4, end4, ProofLevel::Top);
    [[maybe_unused]] auto [ge5, le5] = logger.introduce_bits_of(WPBSum{} + 1_i * s5 + (-1_i) * l5, end5, ProofLevel::Top);
    [[maybe_unused]] auto [ge6, le6] = logger.introduce_bits_of(WPBSum{} + 1_i * s6 + 1_i * l6, end6, ProofLevel::Top);
    [[maybe_unused]] auto [ge7, le7] = logger.introduce_bits_of(WPBSum{} + 1_i * s7a + 1_i * s7b + 1_i * s7c, end7, ProofLevel::Top);
    [[maybe_unused]] auto [ge8, le8] = logger.introduce_bits_of(WPBSum{} + (-1_i) * x8a + (-1_i) * x8b + (-1_i) * x8c, end8, ProofLevel::Top);
    [[maybe_unused]] auto [ge9, le9] = logger.introduce_bits_of(WPBSum{} + 1_i * s9 + 1_i * x9a + 1_i * x9b + 1_i * x9c, end9, ProofLevel::Top);
    [[maybe_unused]] auto [ge10, le10] = logger.introduce_bits_of(WPBSum{} + 1_i * x10a + 1_i * x10b + 1_i * x10c, end10, ProofLevel::Top);

    logger.conclude_none();
    tracker.finalise();

    return 0;
}
