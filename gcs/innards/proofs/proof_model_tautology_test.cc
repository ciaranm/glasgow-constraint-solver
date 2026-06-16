#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>

#include <sstream>

using std::ostringstream;

using namespace gcs;
using namespace gcs::innards;

// Issue #264: a clause whose only content is a statically-true literal is a
// tautology with an empty left-hand side. add_constraint must still emit a
// trivially-true `>= 0` constraint and return a usable line for it, rather than
// returning nothing -- which is why no add_constraint overload is optional any
// more. The emitted constraint must parse in the OPB and stay referenceable from
// a later proof step, so here we reference its line in a pol step; VeriPB rejects
// the proof if the line is missing or the empty constraint is malformed.
auto main() -> int
{
    ProofOptions proof_options{"proof_model_tautology_test"};

    NamesAndIDsTracker tracker(proof_options);
    ProofModel model(proof_options, tracker);

    // A variable so the model is not degenerate; the tautology stands on its own
    // and does not mention it.
    [[maybe_unused]] auto x = model.create_proof_only_integer_variable(
        0_i, 10_i, "x", IntegerVariableProofRepresentation::Bits);

    auto tautology_line = model.add_constraint(Literals{TrueLiteral{}});

    model.finalise();

    ProofLogger logger(proof_options, tracker);
    tracker.switch_from_model_to_proof(&logger);
    logger.start_proof(model);
    tracker.emit_delayed_proof_steps();

    // The tautology's line must be referenceable: re-deriving it by pol succeeds
    // only if it was emitted and is well-formed.
    ostringstream ref;
    ref << tautology_line;
    logger.emit_proof_line("pol " + ref.str() + " ;", ProofLevel::Current);

    logger.conclude_none();
    tracker.finalise();

    return 0;
}
