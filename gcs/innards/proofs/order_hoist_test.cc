#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>

#include <gcs/integer.hh>
#include <gcs/proof.hh>
#include <gcs/variable_id.hh>

#include <iostream>
#include <string>

using namespace gcs;
using namespace gcs::innards;

using std::cerr;
using std::string;

// The second of the two verified foundations the order-encoding-deletion design rests on
// (dev_docs/brancher-design.md, "Bookkeeping mirrors"): the HOIST primitive. Moving a
// search-introduced `ge` definition to a shallower proof level must leave it both live
// *and chained*, so that a later backtrack past its original level does not strand it.
//
// Everything that survives a backtrack in this design -- the backtrack clause's guess
// literals, a learned nogood's decisions, the objective threshold a `soli` names -- gets
// there by hoisting, so a hoist that relocated the definition but lost the chain would
// silently cost every one of those a re-introduction, or worse, leave a Top line naming a
// literal unit propagation can no longer reach.
//
// The variable is a genuine bits-encoded SimpleIntegerVariableID (which is what the
// Literals mode tracks) in [0, 63], with the boundaries and one interior survivor s = ge(10)
// introduced at Top. The deep threshold h = ge(30) is introduced at level 3, and is placed
// with NO deletable literal between it and s, so the forget-time re-stitch never fires a
// stitch that would re-chain h by accident: the only thing that can keep h chained across
// the backtrack is the hoist's own re-stitch. That is what makes the hoist load-bearing
// here rather than decorative.
//
// The probe is a chain-closure RUP ~(x >= h) OR (x >= s) -- reason {x >= h} |- x >= s --
// which VeriPB can close only through a surviving chain link. It is emitted as a raw line
// on purpose: naming x >= h through the normal path would trigger the Literals mode's
// on-demand re-introduction and resurrect exactly the definition the control is trying to
// observe the absence of.
//
// Five scenarios, of which two are controls that must be REJECTED (registered through
// run_test_and_expect_rejection.bash):
//
//   top        hoist h to Top, forget 3/2/1, probe          -> VERIFIED
//   no_hoist   identical but no hoist: the forget deletes h -> REJECTED
//   level      hoist h to level 1, forget 3/2, probe        -> VERIFIED
//   level_gone as level, then forget level 1 as well        -> REJECTED
//   multi      out-of-order hoists into, then out of, a level -> VERIFIED
//
// `multi` covers the bucket-ordering half of the primitive: two deep literals h1 = ge(25)
// < h2 = ge(45) are introduced at level 3 (so h1's definition line ids precede h2's) and
// then hoisted to level 1 in the REVERSE order, h2 first, so h1's smaller ids have to slot
// in front of ids already in that bucket rather than be appended past them
// (ProofLogger::move_proof_lines_to_level's general-position insert, not insert_at_end).
// Then -- and this is the part that makes the invariant observable rather than notional --
// h1 is hoisted on again, to Top, so something finally has to *find* its ids in that
// bucket. Replacing the sorted insert with insert_at_end leaves the bucket unsorted, the
// erase misses, h1's definition stays behind at level 1 and is deleted by the forget, and
// the probe rejects with "constraint ... has already been deleted". Confirmed by mutation:
// without that final hoist, the corrupted bucket is never queried and the scenario passes
// against the broken code.
auto main(int argc, char * argv[]) -> int
{
    bool prove = false;
    string basename = "order_hoist_test";
    string scenario = "top";
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
    if (scenario != "top" && scenario != "no_hoist" && scenario != "level" && scenario != "level_gone" && scenario != "multi") {
        cerr << "unrecognised scenario '" << scenario << "'\n";
        return 1;
    }

    // Nothing here exists outside the proof, so with proving off there is nothing to do.
    if (! prove)
        return 0;

    const SimpleIntegerVariableID x{0ull};
    const Integer s{10_i}; // surviving interior threshold, resident at Top
    const Integer h{30_i}; // deep threshold, hoisted or (control) deleted

    ProofOptions proof_options{basename};
    // Mode and gate set in code, not through GCS_DELETE_ORDER_ENCODING, so the test does
    // not depend on the environment -- and in particular so it runs at gate 0, which the
    // shipped default of 16 would make vacuous here (one variable naming a handful of
    // thresholds would never cross it, and every definition would stay resident).
    proof_options.set_order_encoding_deletion(OrderEncodingDeletion::Literals).set_order_encoding_deletion_min_chain(0);

    NamesAndIDsTracker tracker(proof_options);
    ProofModel model(proof_options, tracker);
    tracker.start_writing_model(&model);

    model.set_up_integer_variable(x, 0_i, 63_i, "x", IntegerVariableProofRepresentation::Bits);

    model.finalise();

    ProofLogger logger(proof_options, tracker);
    tracker.switch_from_model_to_proof(&logger);
    logger.start_proof(model);
    tracker.emit_delayed_proof_steps();

    // The probe is built as raw text, and -- crucially -- built while both of its atoms are
    // still live, then emitted later. Naming an atom through the tracker after the forget
    // would not work at all in a control: deletion *retires* the atom out of the naming
    // table, so pb_file_string_for would throw rather than produce the line VeriPB is meant
    // to reject. Capturing first is also what makes the pairing honest -- a control emits
    // the identical probe to its positive twin, so the hoist is the only difference between
    // the two runs.
    auto probe_text = [&](Integer from, Integer to) {
        return "rup 1 " + tracker.pb_file_string_for(x < from) + " 1 " + tracker.pb_file_string_for(x >= to) + " >= 1 ;";
    };

    // Level 0 (Top): the boundaries and the surviving interior threshold.
    tracker.need_gevar(x, 0_i);  // ge(lower): pinned true
    tracker.need_gevar(x, 64_i); // ge(ub + 1): pinned false
    tracker.need_gevar(x, s);

    // Descend and introduce the deep threshold, so its definition and its chain links to
    // its neighbours all land at level 3.
    logger.enter_proof_level(1);
    logger.enter_proof_level(2);
    logger.enter_proof_level(3);
    tracker.need_gevar(x, h);

    if (scenario == "top" || scenario == "no_hoist") {
        auto probe = probe_text(h, s);
        // The only difference between the two: with the hoist, ge(h) moves to Top and
        // survives; without it the backtrack deletes it and stitches s..ge(64) over it.
        if (scenario == "top")
            tracker.hoist_order_literal_to_top(x, h);
        logger.forget_proof_level(3);
        logger.forget_proof_level(2);
        logger.forget_proof_level(1);
        logger.enter_proof_level(0);
        logger.emit_proof_line(probe, ProofLevel::Current);
    }
    else if (scenario == "level" || scenario == "level_gone") {
        auto probe = probe_text(h, s);
        tracker.hoist_order_literal_to_level(x, h, 1);
        logger.forget_proof_level(3);
        logger.forget_proof_level(2);
        // level_gone goes one further and forgets the level ge(h) was hoisted TO: hoisting
        // delays deletion, it does not prevent it, so the literal must really go there.
        if (scenario == "level_gone") {
            logger.forget_proof_level(1);
            logger.enter_proof_level(0);
        }
        else
            logger.enter_proof_level(1);
        logger.emit_proof_line(probe, ProofLevel::Current);
    }
    else {
        const Integer h1{25_i}, h2{45_i};
        tracker.need_gevar(x, h1);
        tracker.need_gevar(x, h2);
        auto probe_h1_s = probe_text(h1, s);

        // Hoist to a common shallower level in the corrupting order: h2 (whose definition
        // line ids are larger) first, so h1's smaller ids must then slot in front of it.
        tracker.hoist_order_literal_to_level(x, h2, 1);
        tracker.hoist_order_literal_to_level(x, h1, 1);

        // Now take h1 out of that bucket again, by hoisting it on to Top. This is the step
        // that makes the ordering load-bearing rather than cosmetic: an unsorted bucket is
        // harmless until something has to *find* a line in it, and this is that something.
        // If h1's ids were appended past h2's instead of slotted in front, the erase here
        // misses them, they stay behind in level 1, and the forget below deletes the
        // definition of a literal that is supposed to be resident at Top.
        tracker.hoist_order_literal_to_top(x, h1);

        logger.forget_proof_level(3);
        logger.forget_proof_level(2);
        logger.forget_proof_level(1);
        logger.enter_proof_level(0);

        // h1 survived two hoists and three forgets, and is still chained to the survivor.
        logger.emit_proof_line(probe_h1_s, ProofLevel::Current);
    }

    logger.conclude_none();
    tracker.finalise();

    return 0;
}
