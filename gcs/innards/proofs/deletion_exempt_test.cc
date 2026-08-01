#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>

#include <iostream>
#include <optional>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::cerr;
using std::nullopt;
using std::vector;

// Driver for the stage-C frontier deletion exemption (dev_docs/brancher-design.md,
// "Payload 3"), with the mode and the chain gate set in code so the test does not depend on
// GCS_DELETE_ORDER_ENCODING* -- and in particular runs at gate 0, because at the shipped
// gate of 16 a short chain is held resident anyway and the exemption would be doing nothing
// distinguishable.
//
// The exemption is a POLICY note, not a correctness one: nothing is stranded without it, so
// there is no proof VeriPB could reject to tell you it stopped working. What it claims is a
// residency fact -- an exempt variable's `ge` definitions survive a backtrack that deletes
// an ordinary variable's -- and that is what is asserted here, in C++, both ways round. The
// second half matters as much as the first: an exemption that quietly held *everything*
// resident would suppress the churn it targets and the deletion win with it.
//
// VeriPB still runs over the emitted proof, because the exempt literals are used after the
// forget that would have deleted them: if the exemption ever became a bookkeeping-only lie,
// leaving the definitions deleted while the tracker thought them live, that use would name a
// deleted literal and reject.
auto main() -> int
{
    ProofOptions proof_options{"deletion_exempt_test"};
    proof_options.set_order_encoding_deletion(OrderEncodingDeletion::Literals).set_order_encoding_deletion_min_chain(0);

    NamesAndIDsTracker tracker(proof_options);
    ProofModel model(proof_options, tracker);

    // `obj` stands in for the objective: exempt, so its whole encoding stays resident.
    // `ord` is an ordinary variable and must keep deleting exactly as before.
    SimpleIntegerVariableID obj{0}, ord{1};
    model.set_up_integer_variable(obj, 0_i, 100_i, "obj", nullopt);
    model.set_up_integer_variable(ord, 0_i, 100_i, "ord", nullopt);

    // Model-time note, exactly as ProofModel::minimise makes it for a real objective.
    tracker.note_deletion_exempt(obj);

    model.finalise();

    ProofLogger logger(proof_options, tracker);
    tracker.switch_from_model_to_proof(&logger);
    logger.start_proof(model);
    tracker.emit_delayed_proof_steps();

    int rc = 0;
    auto check = [&](bool ok, const char * what) {
        if (! ok) {
            cerr << "deletion exemption broken: " << what << " (fix the exemption, do not relax the check)\n";
            rc = 1;
        }
    };

    // Interior thresholds only: a boundary literal is resident for its own structural
    // reason and would prove nothing either way.
    logger.enter_proof_level(1);
    for (Integer v = 10_i; v <= 40_i; v += 10_i) {
        tracker.need_gevar(obj, v);
        tracker.need_gevar(ord, v);
    }
    auto obj_before = tracker.live_order_literal_count(obj);
    auto ord_before = tracker.live_order_literal_count(ord);
    check(obj_before >= 4, "the exempt variable did not record its thresholds at all");
    check(ord_before >= 4, "the ordinary variable did not record its thresholds at all");

    logger.forget_proof_level(1);

    // The claim, both ways round.
    check(tracker.live_order_literal_count(obj) == obj_before, "an exempt variable's thresholds were deleted by a backtrack");
    check(tracker.live_order_literal_count(ord) < ord_before, "the exemption held an ORDINARY variable resident too, which would suppress the win");
    for (Integer v = 10_i; v <= 40_i; v += 10_i)
        check(tracker.order_literal_is_live(obj, v), "an exempt threshold went missing across the forget");

    // The exemption against payload 2's pin. Every improving solution hoists the objective's
    // new threshold to Top with a SoliHoist cause, and on an exempt variable that threshold is
    // already Top-resident, so the hoist contributes nothing but the pin -- leaving exactly the
    // sole-pin shape eviction otherwise acts on. The exemption has to outrank it, or it would
    // hold only until the first improving solution, and only for the objective, which is the
    // one variable it exists for. The ordinary variable is the control: the same pin over it
    // must still evict, or the refusal would be a blanket one and stage D's eviction half
    // would be dead everywhere rather than deferring to stage C here.
    tracker.need_gevar(ord, 20_i); // the forget above took the control's copy out
    tracker.hoist_live_order_literals_toward_level(vector<Literal>{obj < 20_i, ord < 20_i}, 0, OrderEncodingResidencyCause::SoliHoist);
    check(! tracker.evict_order_literal(obj, 20_i, OrderEncodingResidencyCause::SoliHoist),
        "an exempt variable's threshold was evicted once a soli pinned it");
    check(tracker.order_literal_is_live(obj, 20_i), "the refused eviction took the threshold out anyway");
    check(tracker.evict_order_literal(ord, 20_i, OrderEncodingResidencyCause::SoliHoist),
        "the same pin over an ORDINARY variable was refused too, so the refusal is not the exemption");

    // ... and the definitions really are still there, not just believed to be: multi-hop
    // order propagation over a chain the forget would otherwise have taken out.
    logger.enter_proof_level(1);
    logger.emit_rup_proof_line(WPBSum{} + 1_i * (obj < 40_i) + 1_i * (obj >= 10_i) >= 1_i, ProofLevel::Current);
    logger.forget_proof_level(1);

    logger.enter_proof_level(0);
    logger.conclude_none();
    tracker.finalise();

    return rc;
}
