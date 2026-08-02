#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
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

// Driver for the stage-B'' eq-atom sliding window (dev_docs/brancher-design.md, "The
// eq-atom window"), run through the production entry points -- mint_windowed_eq_guess,
// backtrack, emit_eq_window_advance -- rather than a hand-written proof, so what VeriPB
// checks here is the solver's own emission. The mode, the chain gate and the window are set
// in code, so the test does not depend on GCS_DELETE_ORDER_ENCODING* being set, and in
// particular runs at gate 0 (the shipped default of 16 would hide the whole thing: no
// variable here names 17 thresholds) and with a window that ships off by default.
//
// Each scenario replays what solve.cc does around one branching node: mint the guess's eq
// definition at the node's level, descend a level and come back, emit the refuted child's
// backtrack clause, then advance the frontier and tidy. What that has to get right, and
// what fails if it does not:
//
//  - **The advance RUPs through the eq atom's reverse reification.** That is the whole
//    mechanism, and it is why the tidy deletes in the order it does; deleting the
//    definition before the advance is what driver control D2c
//    (order-encoding-deletion-artifacts/eq-window) shows VeriPB rejecting.
//  - **No double deletion.** The tidy `del`s the superseded advance, the sibling clause and
//    the definition lines, and the level they sat at is eventually forgotten -- which emits
//    a bare `del id` for a bucket interval of length one. VeriPB errors on a `del id`
//    naming an already-deleted line, so anything the tidy deleted without dropping from its
//    bucket rejects here.
//  - **Re-introduction after eviction.** An evicted atom is re-minted and used again, which
//    emits a fresh `red` against the bits -- the step that fails if something the eviction
//    should have removed is still in the database in a form the witness cannot satisfy.
//  - **The hoist-out rule.** An eq atom that acquires a permanent reference is retained
//    rather than evicted, and is then named by a Top line across a forget of the window's
//    level. That only checks out if the two ge thresholds it names went to Top with it.
//
// And what it checks in C++ instead, because VeriPB *cannot*: the window's actual claim,
// that a branched variable's resident eq and ge definitions stay O(1) rather than growing
// with the domain it is stepping through. A window that quietly stopped evicting would
// still verify -- it would simply be the baseline again -- so the counts are asserted at
// every step, against bounds a baseline run overshoots on the second iteration.
auto main() -> int
{
    ProofOptions proof_options{"eq_window_test"};
    proof_options.set_order_encoding_deletion(OrderEncodingDeletion::Literals)
        .set_order_encoding_deletion_min_chain(0)
        .set_order_encoding_deletion_eq_window();

    NamesAndIDsTracker tracker(proof_options);
    ProofModel model(proof_options, tracker);

    // One variable per scenario, each with its own guard variable, so the scenarios cannot
    // perturb each other's chains. A guard is [0..3] rather than [0..1] so it gets the
    // ordinary bits encoding (a {0,1} variable is direct-only, and carries no order cuts).
    SimpleIntegerVariableID x{0}, gx{1}, y{2}, gy{3}, w{4}, gw{5}, z{6}, gz{7}, p{8}, gp{9};
    model.set_up_integer_variable(x, 0_i, 15_i, "x", nullopt);
    model.set_up_integer_variable(gx, 0_i, 3_i, "gx", nullopt);
    model.set_up_integer_variable(y, 0_i, 15_i, "y", nullopt);
    model.set_up_integer_variable(gy, 0_i, 3_i, "gy", nullopt);
    model.set_up_integer_variable(w, 0_i, 15_i, "w", nullopt);
    model.set_up_integer_variable(gw, 0_i, 3_i, "gw", nullopt);
    model.set_up_integer_variable(z, 0_i, 15_i, "z", nullopt);
    model.set_up_integer_variable(gz, 0_i, 3_i, "gz", nullopt);
    model.set_up_integer_variable(p, 0_i, 15_i, "p", nullopt);
    model.set_up_integer_variable(gp, 0_i, 3_i, "gp", nullopt);

    // The guard is what makes each guess genuinely refutable, so the sibling clause the
    // window's tidy deletes is a real RUP rather than something asserted for the test:
    // `g >= 1` forces the branched variable into the half its guesses are not in.
    // Ascending variables: g >= 1 => var >= 8, so var == 0..7 are all refuted.
    model.add_constraint(WPBSum{} + 8_i * gx + -1_i * x <= 0_i);
    model.add_constraint(WPBSum{} + 8_i * gw + -1_i * w <= 0_i);
    model.add_constraint(WPBSum{} + 8_i * gz + -1_i * z <= 0_i);
    model.add_constraint(WPBSum{} + 8_i * gp + -1_i * p <= 0_i);
    // Descending: g >= 1 => var <= 7, so var == 15..8 are all refuted.
    model.add_constraint(WPBSum{} + 1_i * y + 8_i * gy <= 15_i);

    model.finalise();

    ProofLogger logger(proof_options, tracker);
    tracker.switch_from_model_to_proof(&logger);
    logger.start_proof(model);
    tracker.emit_delayed_proof_steps();

    int rc = 0;
    // Name every check: these assert an invariant the proof cannot show, so a bare exit
    // code would leave a failure undiagnosable -- and the fix for any of them is in the
    // window, never in the bound written here.
    auto check = [&](bool ok, const char * what) {
        if (! ok) {
            cerr << "eq window invariant broken: " << what << " (fix the window, do not relax the check)\n";
            rc = 1;
        }
    };

    // One branching node at proof level 2, under an outer guess made at level 1, exactly as
    // solve.cc lays it out: a frame at depth d runs its branch loop at level d+1, and its
    // children close by re-entering level d+1 to emit their backtrack clause before
    // forgetting level d+2.
    auto refute_sibling = [&](const Literal & outer, const Literal & guess) {
        logger.mint_windowed_eq_guess(guess);
        logger.enter_proof_level(3);
        logger.enter_proof_level(2);
        logger.backtrack(vector<Literal>{outer, guess});
        logger.forget_proof_level(3);
    };

    // ---- x: the ascending window (smallest_first / smallest_in) ----
    logger.enter_proof_level(1);
    Literal outer_x{gx >= 1_i};
    logger.enter_proof_level(2);
    for (Integer v = 0_i; v <= 6_i; ++v) {
        refute_sibling(outer_x, x == v);
        // The atom is windowed while the step is in flight: one live windowed definition,
        // never a second.
        check(tracker.live_windowed_eq_count(x) == 1, "x: the step's eq definition is not windowed");
        logger.emit_eq_window_advance(vector<Literal>{outer_x}, x == v, /*lower=*/true);
        // ... and the step's tidy took it out again. This is the assertion a window that
        // stopped evicting fails: the baseline keeps every eq definition it ever mints.
        check(tracker.live_windowed_eq_count(x) == 0, "x: the tidy did not evict the stepped-over eq definition");
        // The steady state the design targets: the boundary ge(0), the frontier ge(v+1),
        // and nothing else growing with v. ge(v)'s eviction is what keeps this flat -- a
        // baseline run is at v + 2 by now.
        check(tracker.live_order_literal_count(x) <= 3, "x: resident ge count is growing with the domain, not O(1)");
    }
    // Re-introduction: the last refuted value is named again, and re-mints cleanly because
    // the tidy left nothing behind that references it.
    tracker.need_direct_encoding_for(x, 6_i);
    logger.emit_rup_proof_line(WPBSum{} + 1_i * (x != 6_i) + 1_i * (x >= 6_i) >= 1_i, ProofLevel::Current);
    logger.enter_proof_level(1);
    logger.forget_proof_level(2);

    // ---- y: the descending window (largest_first / largest_in), the UpperBound mirror ----
    // Never exercised by the hand-authored driver, which only covered the ascending
    // direction: here the frontier runs the other way, the advance is `y < v` rather than
    // `y >= v+1`, and the threshold stepped over is ge(v+1) rather than ge(v).
    Literal outer_y{gy >= 1_i};
    logger.enter_proof_level(2);
    for (Integer v = 15_i; v >= 9_i; --v) {
        refute_sibling(outer_y, y == v);
        check(tracker.live_windowed_eq_count(y) == 1, "y (descending): the step's eq definition is not windowed");
        logger.emit_eq_window_advance(vector<Literal>{outer_y}, y == v, /*lower=*/false);
        check(tracker.live_windowed_eq_count(y) == 0, "y (descending): the tidy did not evict the stepped-over eq definition");
        check(tracker.live_order_literal_count(y) <= 3, "y (descending): resident ge count is growing with the domain, not O(1)");
    }
    logger.enter_proof_level(1);
    logger.forget_proof_level(2);

    // ---- w: the hoist-out rule ----
    // An eq atom that acquires a permanent (Top) reference -- here the solx/nogood shape,
    // a Top clause naming `w == 2` -- must be retained rather than evicted when the window
    // steps past it, together with the two ge thresholds its definition names.
    Literal outer_w{gw >= 1_i};
    logger.enter_proof_level(2);
    refute_sibling(outer_w, w == 2_i);
    auto w2 = tracker.xliteral_for(w == 2_i);
    check(tracker.live_windowed_eq_count(w) == 1, "w: the guess mint did not window the eq definition");
    // The reference is detected at the reference site, before the Top line is emitted.
    tracker.note_permanent_eq_reference(w, 2_i);
    check(tracker.live_windowed_eq_count(w) == 0, "w: a permanent reference did not take the atom out of the window");
    logger.emit_rup_proof_line(WPBSum{} + 1_i * (w != 2_i) + 1_i * (w >= 2_i) >= 1_i, ProofLevel::Top);
    // The window steps on regardless; its tidy must leave the retained atom alone.
    logger.emit_eq_window_advance(vector<Literal>{outer_w}, w == 2_i, /*lower=*/true);
    check(tracker.xliteral_for(w == 2_i) == w2, "w: the tidy evicted a retained atom");

    refute_sibling(outer_w, w == 3_i);
    logger.emit_eq_window_advance(vector<Literal>{outer_w}, w == 3_i, /*lower=*/true);
    logger.enter_proof_level(1);
    logger.forget_proof_level(2);

    // The retained atom survived the forget, and so must the two thresholds its definition
    // names: this is the discriminating half. Had the hoist-out left them deletable, the
    // forget would have deleted them under the surviving Top definition, and re-introducing
    // them here would emit a `red` that definition's clause refutes.
    check(tracker.xliteral_for(w == 2_i) == w2, "w: the retained atom did not survive the forget");
    tracker.need_gevar(w, 2_i);
    tracker.need_gevar(w, 3_i);
    logger.enter_proof_level(2);
    logger.emit_rup_proof_line(WPBSum{} + 1_i * (w != 2_i) + 1_i * (w < 3_i) >= 1_i, ProofLevel::Current);
    logger.enter_proof_level(1);
    logger.forget_proof_level(2);

    // ---- z: the (i-dynamic) half of the eq-by-interval guard ----
    // An interval literal requested mid-search on a windowed variable makes the partition
    // machinery name every one of its eq atoms from Top lines. The window has to collapse
    // first -- every live windowed definition hoisted out to Top -- or those Top lines
    // would name definitions the next backtrack deletes.
    Literal outer_z{gz >= 1_i};
    logger.enter_proof_level(2);
    refute_sibling(outer_z, z == 4_i);
    auto z4 = tracker.xliteral_for(z == 4_i);
    check(tracker.live_windowed_eq_count(z) == 1, "z: the guess mint did not window the eq definition");
    [[maybe_unused]] auto in_lit = tracker.need_invar(z, 4_i, 9_i);
    check(tracker.live_windowed_eq_count(z) == 0, "z: an interval request did not collapse the live window");
    // And the variable stays unwindowed: a later guess mint on it gets a permanent
    // definition, so the partition can never be left naming a deletable one.
    logger.mint_windowed_eq_guess(z == 5_i);
    check(tracker.live_windowed_eq_count(z) == 0, "z: a variable with an interval partition was windowed again");
    logger.enter_proof_level(1);
    logger.forget_proof_level(2);
    // Both atoms outlived the forget, which they only do if the collapse made them
    // permanent.
    check(tracker.xliteral_for(z == 4_i) == z4, "z: the collapsed window's atom did not survive the forget");
    logger.emit_rup_proof_line(WPBSum{} + 1_i * (z != 4_i) + 1_i * (z >= 4_i) >= 1_i, ProofLevel::Current);
    logger.emit_rup_proof_line(WPBSum{} + 1_i * (z != 5_i) + 1_i * (z >= 5_i) >= 1_i, ProofLevel::Current);

    // ---- p: a reference reached only through a `pol`'s operands ----
    // The all-different Hall-set shape, which is what `magic_square --size=4
    // --all-different gac` rejected on: pairwise at-most-one lines naming `p == 2` are
    // emitted at Temporary, then folded by a PolBuilder into a line that lands at Top. The
    // resulting constraint names `p == 2`, but nothing in the emitted `pol` text does --
    // the literals are the arithmetic's result -- so the reference is invisible to any
    // walk over the line, and before the operand-union rule nothing pinned the atom.
    //
    // The discriminating assertion is the count, not the proof: with the reference missed,
    // the atom stays windowed and gets evicted, and only *then* does VeriPB reject. A test
    // that checked verification alone would be reporting the symptom two steps downstream.
    Literal outer_p{gp >= 1_i};
    logger.enter_proof_level(2);
    refute_sibling(outer_p, p == 2_i);
    auto p2 = tracker.xliteral_for(p == 2_i);
    check(tracker.live_windowed_eq_count(p) == 1, "p: the guess mint did not window the eq definition");

    {
        // Operands at Temporary, exactly as all_different/justify.cc emits them, and both
        // genuinely RUP: `p == 2` implies `p >= 2` through the eq definition, and the guard
        // constraint `8*gp <= p` refutes `p == 2` once `gp >= 1`. Their own level pins
        // nothing -- it is the pol they feed that is permanent.
        PolBuilder am1;
        am1.add(logger.emit_rup_proof_line(WPBSum{} + 1_i * (p != 2_i) + 1_i * (p >= 2_i) >= 1_i, ProofLevel::Temporary));
        am1.add(logger.emit_rup_proof_line(WPBSum{} + 1_i * (p != 2_i) + 1_i * (gp < 1_i) >= 1_i, ProofLevel::Temporary));
        am1.saturate();
        check(tracker.live_windowed_eq_count(p) == 1, "p: a Temporary operand should not pin on its own");
        am1.emit(logger, ProofLevel::Top);
    }

    check(tracker.live_windowed_eq_count(p) == 0, "p: a Top pol over operands naming the atom did not take it out of the window");

    // The window steps on regardless; the retained atom must survive both the tidy and the
    // forget, as in scenario w.
    logger.emit_eq_window_advance(vector<Literal>{outer_p}, p == 2_i, /*lower=*/true);
    check(tracker.xliteral_for(p == 2_i) == p2, "p: the tidy evicted an atom a pol had pinned");

    refute_sibling(outer_p, p == 3_i);
    logger.emit_eq_window_advance(vector<Literal>{outer_p}, p == 3_i, /*lower=*/true);
    logger.enter_proof_level(1);
    logger.forget_proof_level(2);
    check(tracker.xliteral_for(p == 2_i) == p2, "p: the pol-pinned atom did not survive the forget");
    // Naming it again after the forget is the step that rejects if the ge thresholds its
    // definition names were left deletable.
    tracker.need_gevar(p, 2_i);
    tracker.need_gevar(p, 3_i);
    logger.enter_proof_level(2);
    logger.emit_rup_proof_line(WPBSum{} + 1_i * (p != 2_i) + 1_i * (p < 3_i) >= 1_i, ProofLevel::Current);
    logger.enter_proof_level(1);
    logger.forget_proof_level(2);

    logger.enter_proof_level(0);
    logger.conclude_none();
    tracker.finalise();

    return rc;
}
