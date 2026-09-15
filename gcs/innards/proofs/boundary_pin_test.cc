#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>

#include <fstream>
#include <iostream>
#include <regex>
#include <string>

using namespace gcs;
using namespace gcs::innards;

// Inv-Bound (dev_docs/literal-encodings.tex) asks for one boundary pin a side:
// the unit for the largest defined order cut at or below the declared lower
// bound, and for the smallest above the declared upper. Every other
// out-of-range cut follows from that one by the order chain, so the solver
// needs to write down two units per variable however many out-of-range cuts it
// creates. It used to write one per cut --- 2,258 of them over 68
// variable-and-side pairs on the tsp example --- which is issue #927.
//
// Nothing else in the suite would notice a return to that: extra units are
// sound, so every proof still verifies and the only symptom is size. Hence a
// lane that reads the proof back and counts.
//
// Two variables, each given a run of out-of-range cuts in an adversarial order
// --- ascending on the lower side, which is the case that defeats "pin the
// extreme cut of whatever is defined so far", and descending on the upper.
// Neither declared bound's own cut is requested, so the pinned one has to be
// created in the proof rather than found; x's is reachable from the requests
// above it through the chain and y's from below.
auto main() -> int
{
    ProofOptions proof_options{"boundary_pin_test"};

    NamesAndIDsTracker tracker(proof_options);
    ProofModel model(proof_options, tracker);

    auto x = model.create_proof_only_integer_variable(0_i, 30_i, "x", IntegerVariableProofRepresentation::Bits);
    auto y = model.create_proof_only_integer_variable(0_i, 30_i, "y", IntegerVariableProofRepresentation::Bits);

    model.finalise();

    ProofLogger logger(proof_options, tracker);
    tracker.switch_from_model_to_proof(&logger);
    logger.start_proof(model);
    tracker.emit_delayed_proof_steps();

    // Below x's declared lower bound, ascending towards it but never reaching it.
    for (Integer v = -12_i; v <= -1_i; ++v)
        tracker.need_proof_name(x >= v);

    // Above y's declared upper bound, descending towards it but never reaching it.
    for (Integer v = 44_i; v >= 32_i; --v)
        tracker.need_proof_name(y >= v);

    // What the pins are for: each out-of-range fact is still reachable, which is
    // the half of this that VeriPB checks. Stated as two-literal clauses so they
    // cannot be mistaken for pins by the count below --- and so that the check
    // is a propagation rather than the trivial `pol` of a unit against itself.
    for (Integer v = -12_i; v <= -1_i; ++v)
        logger.emit_rup_proof_line(WPBSum{} + 1_i * (x >= v) + 1_i * (y >= 32_i) >= 1_i, ProofLevel::Current);
    for (Integer v = 44_i; v >= 32_i; --v)
        logger.emit_rup_proof_line(WPBSum{} + 1_i * ! (y >= v) + 1_i * (x >= -12_i) >= 1_i, ProofLevel::Current);

    logger.conclude_none();
    tracker.finalise();

    // A boundary pin is a top-level unit RUP over a single order atom, which in
    // this proof nothing else is: the clauses above have two literals apiece and
    // the definitions are `red`. Counting the emitted text rather than asking the
    // tracker is deliberate --- the tracker would report what it meant to do, and
    // the thing worth fixing was how many lines came out.
    std::ifstream proof{proof_options.proof_file_names.proof_file};
    if (! proof) {
        std::cerr << "could not read back " << proof_options.proof_file_names.proof_file << "\n";
        return 1;
    }

    const std::regex pin{R"(^rup 1 [^ ]+ >= 1;$)"};
    int pins = 0;
    for (std::string line; std::getline(proof, line);)
        if (std::regex_match(line, pin))
            ++pins;

    // One a side, over two variables that each use one side.
    if (pins != 2) {
        std::cerr << "expected 2 boundary pins (one a side, Inv-Bound), got " << pins << "\n";
        return 1;
    }

    return 0;
}
