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

    model.finalise();

    ProofLogger logger(proof_options, tracker);
    tracker.switch_from_model_to_proof(&logger);
    logger.start_proof(model);
    tracker.emit_delayed_proof_steps();

    // The 2m reds. The returned pair is BinEnc(end) >= s + l / <= s + l; we don't
    // need to reference them here --- VeriPB has already verified each step.
    [[maybe_unused]] auto [ge, le] = logger.introduce_bits_of(WPBSum{} + 1_i * s + 1_i * l, end, ProofLevel::Top);

    logger.conclude_none();
    tracker.finalise();

    return 0;
}
