#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>

using namespace gcs;
using namespace gcs::innards;

// Issue #264: a clause whose only content is a statically-true literal is a
// tautology with an empty left-hand side. The proof model must still emit a
// trivially-true `>= 0` constraint for it, rather than omitting it. The emitted
// constraint must parse in the OPB and stay referenceable from a later proof
// step, so here we add it under an @label and reference that label in a pol step;
// VeriPB rejects the proof if the label is missing or the constraint malformed.
auto main() -> int
{
    ProofOptions proof_options{"proof_model_tautology_test"};

    NamesAndIDsTracker tracker(proof_options);
    ProofModel model(proof_options, tracker);

    // A variable so the model is not degenerate; the tautology stands on its own
    // and does not mention it.
    [[maybe_unused]] auto x = model.create_proof_only_integer_variable(0_i, 10_i, "x", IntegerVariableProofRepresentation::Bits);

    model.add_labelled_constraint("tautology", Literals{TrueLiteral{}});

    model.finalise();

    ProofLogger logger(proof_options, tracker);
    tracker.switch_from_model_to_proof(&logger);
    logger.start_proof(model);
    tracker.emit_delayed_proof_steps();

    // The tautology must be referenceable: re-deriving it by pol succeeds only if
    // it was emitted and is well-formed. Reference it by @label.
    logger.emit_proof_line("pol @tautology ;", ProofLevel::Current);

    logger.conclude_none();
    tracker.finalise();

    return 0;
}
