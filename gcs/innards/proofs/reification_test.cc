#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <vector>

using std::vector;

using namespace gcs;
using namespace gcs::innards;

auto main() -> int
{
    ProofOptions proof_options{"reification_test"};

    NamesAndIDsTracker tracker(proof_options);
    ProofModel model(proof_options, tracker);

    vector<PseudoBooleanTerm> terms = {TrueLiteral{}, model.create_proof_flag("t"),
        model.create_proof_only_integer_variable(1_i, 10_i, "x", IntegerVariableProofRepresentation::Bits)};

    auto reif = HalfReifyOnConjunctionOf{FalseLiteral{}, model.create_proof_flag("r")};

    auto constr = WPBSum{} + 5_i * TrueLiteral{} + 3_i * model.create_proof_flag("t") +
            -2_i * model.create_proof_only_integer_variable(1_i, 10_i, "x", IntegerVariableProofRepresentation::Bits) >=
        4_i;

    // Reference the constraint by @label rather than by relative line number, so
    // the test does not depend on the constraint's position in the OPB.
    model.add_labelled_constraint("test", tracker.reify(constr, HalfReifyOnConjunctionOf{reif}));

    model.finalise();

    ProofLogger logger(proof_options, tracker);

    logger.start_proof(model);

    // Check that after saturation, a reification by a false literal is trivially true.
    // The pol references the constraint by @label; the `e` references the pol's own
    // output (the immediately preceding line), which is a robust proof-internal ref.
    logger.emit_proof_line("pol @test s;", ProofLevel::Current);
    logger.emit_proof_line("e >= -35 : -1;", ProofLevel::Current);
    logger.conclude_none();
    tracker.finalise();
}
