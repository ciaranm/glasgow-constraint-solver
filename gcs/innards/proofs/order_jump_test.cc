#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>

#include <gcs/integer.hh>

#include <iostream>
#include <string>

using namespace gcs;
using namespace gcs::innards;

using std::cerr;
using std::string;

// The first of the two verified foundations the order-encoding-deletion design rests on
// (dev_docs/order-encoding-deletion.md; dev_docs/brancher-design.md, "The decision and its
// backtrack advance"): a bound jump over a run of holes is RUP from a reason naming only
// the *guesses* that created the holes, not the holes themselves.
//
// That is what lets the framework justify a bound advance with a short reason instead of
// one literal per removed value, and it is the reason the order encoding can be deleted at
// all: the surviving chain plus the eq reverse-reification axioms are enough for unit
// propagation to climb the bound one hole at a time. If VeriPB ever stopped closing this,
// every advance in the design would need re-deriving, so it is checked here rather than
// left to a scratch driver.
//
// The model is built purely at the proof-logging layer (like invar_test): a Bits-encoded
// proof-only variable x in [0, 63], a proof flag g, and the holes posted as *reified* model
// axioms ~g OR (x != v) for every v in [L, H). Reified, not unconditional, is the whole
// point -- the eliminations have to be derivable from g rather than baked into the model,
// or the jump would be trivial and the test would prove nothing.
//
// Two controls, because the positive scenario alone would pass against a checker that
// accepted anything: `no_flag` drops g from the reason (so the holes are no longer
// derivable and the jump is unsound), and `over_jump` claims one value too many (x = H is
// still in the domain). Both must be REJECTED by VeriPB, which is why they are registered
// through run_test_and_expect_rejection.bash with the message they must reject with.
namespace
{
    const Integer hole_run_lo{10_i}; // first eliminated value
    const Integer hole_run_hi{20_i}; // first surviving value above the run
}

auto main(int argc, char * argv[]) -> int
{
    bool prove = false;
    string basename = "order_jump_test";
    string scenario = "jump";
    for (int arg = 1; arg < argc; ++arg) {
        string a{argv[arg]};
        if (a == "--prove")
            prove = true;
        else if (a == "--proof-files-basename" && arg + 1 < argc)
            basename = argv[++arg];
        else if (a == "--scenario" && arg + 1 < argc)
            scenario = argv[++arg];
        else {
            cerr << "unrecognised argument '" << a << "'\n";
            return 1;
        }
    }
    if (scenario != "jump" && scenario != "no_flag" && scenario != "over_jump") {
        cerr << "unrecognised scenario '" << scenario << "'\n";
        return 1;
    }

    // Nothing here exists outside the proof, so with proving off there is nothing to do.
    if (! prove)
        return 0;

    ProofOptions proof_options{basename};

    NamesAndIDsTracker tracker(proof_options);
    ProofModel model(proof_options, tracker);
    tracker.start_writing_model(&model);

    auto x = model.create_proof_only_integer_variable(0_i, 63_i, "x", IntegerVariableProofRepresentation::Bits);
    auto g = model.create_proof_flag("g");

    // The holes, reified on g: g -> (x != v), i.e. ~g OR (x != v).
    for (Integer v = hole_run_lo; v < hole_run_hi; v = v + 1_i)
        model.add_constraint(WPBSum{} + 1_i * (! g) + 1_i * (x != v) >= 1_i);

    model.finalise();

    ProofLogger logger(proof_options, tracker);
    tracker.switch_from_model_to_proof(&logger);
    logger.start_proof(model);
    tracker.emit_delayed_proof_steps();

    if (scenario == "jump") {
        // reason {g, x >= lo} |- x >= hi. Sound: each (x >= v) with (x != v) unit-propagates
        // to (x >= v+1) through the eq atom's reverse-reification axiom, so the bound climbs
        // the whole run without the reason ever naming a hole.
        logger.emit_rup_proof_line(WPBSum{} + 1_i * (! g) + 1_i * ! (x >= hole_run_lo) + 1_i * (x >= hole_run_hi) >= 1_i, ProofLevel::Current);
    }
    else if (scenario == "no_flag") {
        // reason {x >= lo}, with g dropped: the holes are no longer derivable, so nothing
        // stops x from sitting inside the run. Must be REJECTED.
        logger.emit_rup_proof_line(WPBSum{} + 1_i * ! (x >= hole_run_lo) + 1_i * (x >= hole_run_hi) >= 1_i, ProofLevel::Current);
    }
    else {
        // reason {g, x >= lo} |- x >= hi + 1: one value too far, since x = hi survives.
        // Must be REJECTED.
        logger.emit_rup_proof_line(
            WPBSum{} + 1_i * (! g) + 1_i * ! (x >= hole_run_lo) + 1_i * (x >= (hole_run_hi + 1_i)) >= 1_i, ProofLevel::Current);
    }

    logger.conclude_none();
    tracker.finalise();

    return 0;
}
