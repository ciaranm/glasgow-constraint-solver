#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>

#include <optional>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::nullopt;
using std::vector;

using Cause = OrderEncodingResidencyCause;

// Driver for the stage-B' order-encoding eviction primitives (see
// dev_docs/brancher-design.md), with the deletion mode and the chain gate set in code so
// the test does not depend on GCS_DELETE_ORDER_ENCODING* being set -- and, in particular,
// so it runs at the aggressive gate 0, which the shipped default of 16 would otherwise
// hide entirely (four small variables never name 17 thresholds, so every definition would
// stay resident and nothing here would be exercised).
//
// What VeriPB is checking, beyond the return values:
//
//  - **Re-introduction after eviction.** Each eviction is followed by a `need_gevar` /
//    `need_direct_encoding_for` for the same atom, which re-emits its `red` reification
//    pair against the bits -- the step that fails if anything the eviction should have
//    removed is still in the constraint database in a form the witness cannot satisfy.
//  - **No double deletion.** Every level an eviction has taken lines out of is eventually
//    forgotten, and forget_proof_level emits a bare `del id` for a bucket interval of
//    length one. VeriPB errors on a `del id` naming an already-deleted line, so an
//    eviction that deleted a line without dropping it from its level bucket rejects (the
//    `u` scenario is shaped to put an evicted line in exactly that position).
//  - **The eq hoist-out rule.** eq(10) on `w` is hoisted out of the window to Top and then
//    named by a Top line across a forget of the window's level. That only checks out if
//    hoist_eq_to_top brought the two ge thresholds the eq definition names to Top with it.
//
// And what it deliberately checks in C++ instead, because VeriPB *cannot*: that eviction
// leaves no chain clause naming the threshold it removed. A leftover clause stays a valid
// derived constraint, so the proof still verifies with one -- measured, by mutation -- and
// the loss is silent: exactly the resident-database shrinkage the mode exists for. See
// NamesAndIDsTracker::chain_clauses_naming.
auto main() -> int
{
    ProofOptions proof_options{"order_evict_test"};
    proof_options.set_order_encoding_deletion(OrderEncodingDeletion::Literals).set_order_encoding_deletion_min_chain(0);

    NamesAndIDsTracker tracker(proof_options);
    ProofModel model(proof_options, tracker);

    // One variable per scenario, so the scenarios cannot perturb each other's chains.
    SimpleIntegerVariableID x{0}, y{1}, z{2}, w{3}, u{4}, t{5}, v{6};
    model.set_up_integer_variable(x, 0_i, 100_i, "x", nullopt);
    model.set_up_integer_variable(y, 0_i, 100_i, "y", nullopt);
    model.set_up_integer_variable(z, 0_i, 100_i, "z", nullopt);
    model.set_up_integer_variable(w, 0_i, 100_i, "w", nullopt);
    model.set_up_integer_variable(u, 0_i, 100_i, "u", nullopt);
    model.set_up_integer_variable(t, 0_i, 100_i, "t", nullopt);
    model.set_up_integer_variable(v, 0_i, 100_i, "v", nullopt);

    model.finalise();

    ProofLogger logger(proof_options, tracker);
    tracker.switch_from_model_to_proof(&logger);
    logger.start_proof(model);
    tracker.emit_delayed_proof_steps();

    int rc = 0;
    auto check = [&](bool ok) {
        if (! ok)
            rc = 1;
    };

    // ---- x: mid-level eviction (the eq window's per-iteration tidy shape) ----
    logger.enter_proof_level(1);
    tracker.need_gevar(x, 20_i);
    tracker.need_gevar(x, 40_i);
    tracker.need_gevar(x, 60_i);
    auto x40 = tracker.xliteral_for(x >= 40_i);

    // Two chain clauses over 40 (to 20 and to 60), and one over 20.
    check(tracker.chain_clauses_naming(x, 40_i) == 2);
    check(tracker.chain_clauses_naming(x, 20_i) == 1);

    // A deletable threshold has no Top pin, so naming a Top cause for it is refused.
    check(! tracker.evict_order_literal(x, 40_i, Cause::SoliHoist));
    // With no cause named it goes: its definition and the two chain clauses over it are
    // deleted now instead of at the backtrack that would have deleted them, and its
    // surviving neighbours 20 and 60 are stitched.
    check(tracker.evict_order_literal(x, 40_i, nullopt));
    // Eviction retires the atom, so nothing can name it until it is re-introduced.
    check(! tracker.find_xliteral_for(x >= 40_i).has_value());
    // Nothing names it any more, and 20 has traded its clause to 40 for the skip link.
    check(tracker.chain_clauses_naming(x, 40_i) == 0);
    check(tracker.chain_clauses_naming(x, 20_i) == 1);

    tracker.need_gevar(x, 40_i);
    // Re-introduction takes the retired XLiteral back: a fresh one would render as the
    // same verbose name but a different x<n> with verbose names off.
    check(tracker.xliteral_for(x >= 40_i) == x40);
    // Multi-hop order propagation over the re-stitched chain.
    logger.emit_rup_proof_line(WPBSum{} + 1_i * (x < 60_i) + 1_i * (x >= 20_i) >= 1_i, ProofLevel::Current);
    logger.forget_proof_level(1);

    // ---- y: eviction from Top under a sole pin (payload 2's shape) ----
    logger.enter_proof_level(1);
    tracker.need_gevar(y, 30_i);
    tracker.need_gevar(y, 50_i);
    tracker.need_gevar(y, 70_i);
    auto y50 = tracker.xliteral_for(y >= 50_i);

    // What ProofLogger::solution does for the objective threshold of a new incumbent:
    // hoist it to Top, where the improvement constraint can name it permanently.
    tracker.hoist_live_order_literals_toward_level(vector<Literal>{y >= 50_i}, 0, Cause::SoliHoist);

    // A Top-resident threshold is only evictable against a named cause that is its sole
    // pin: no cause, or the wrong cause, is refused.
    check(! tracker.evict_order_literal(y, 50_i, nullopt));
    check(! tracker.evict_order_literal(y, 50_i, Cause::NogoodHoist));
    check(tracker.evict_order_literal(y, 50_i, Cause::SoliHoist));
    check(! tracker.find_xliteral_for(y >= 50_i).has_value());
    // The clauses over it go with it -- including the ones the hoist to Top emitted, which
    // sit at a different level from the ones its introduction did.
    check(tracker.chain_clauses_naming(y, 50_i) == 0);

    tracker.need_gevar(y, 50_i);
    check(tracker.xliteral_for(y >= 50_i) == y50);
    logger.emit_rup_proof_line(WPBSum{} + 1_i * (y < 70_i) + 1_i * (y >= 30_i) >= 1_i, ProofLevel::Current);
    logger.forget_proof_level(1);

    // ---- z: what the Top-pin bookkeeping must refuse ----
    logger.enter_proof_level(1);
    // eq(50) names ge(50) and ge(51); eq(51) names ge(51) and ge(52). ge(51) is therefore
    // pinned at Top by two distinct permanent atoms, and both pins have the same cause --
    // which is why the count is kept at the reference site rather than inside the hoist,
    // whose early return for an already-Top threshold sees the second one not at all.
    tracker.need_direct_encoding_for(z, 50_i);
    tracker.need_direct_encoding_for(z, 51_i);
    check(! tracker.evict_order_literal(z, 51_i, Cause::EqHoist));
    check(! tracker.evict_order_literal(z, 51_i, Cause::SoliHoist));
    // ge(0) is the lower boundary literal: resident from birth, never hoisted, so it takes
    // no pin -- and "Top with no pin" must read as structurally resident and unevictable,
    // not as unpinned and free. Evicting a chain anchor would be far worse than not
    // winning.
    tracker.need_direct_encoding_for(z, 0_i);
    check(! tracker.evict_order_literal(z, 0_i, Cause::EqHoist));
    check(! tracker.evict_order_literal(z, 0_i, nullopt));
    logger.forget_proof_level(1);

    // ---- w: the eq-atom window's hoist-out rule and forget sweep ----
    logger.enter_proof_level(1);
    // Two windowed eq atoms: definitions at Current, and their ge thresholds left
    // deletable rather than hoisted to Top. The scope is the branch layer's request, held
    // across the guess mint and nothing else.
    {
        NamesAndIDsTracker::WindowedEqScope scope{tracker};
        tracker.need_direct_encoding_for(w, 10_i);
        tracker.need_direct_encoding_for(w, 20_i);
    }
    auto w10 = tracker.xliteral_for(w == 10_i);
    auto w20 = tracker.xliteral_for(w == 20_i);
    check(tracker.live_windowed_eq_count(w) == 2);

    // eq(10) acquires a permanent reference, so the window retains it instead of evicting
    // it: its definition and the two ge thresholds it names all move to Top.
    tracker.hoist_eq_to_top(w, 10_i);
    logger.emit_rup_proof_line(WPBSum{} + 1_i * (w != 10_i) + 1_i * (w >= 10_i) >= 1_i, ProofLevel::Top);

    logger.forget_proof_level(1);

    // eq(20) stayed windowed, so the forget deleted its definition and retired it.
    check(! tracker.find_xliteral_for(w == 20_i).has_value());
    tracker.need_direct_encoding_for(w, 20_i);
    check(tracker.xliteral_for(w == 20_i) == w20);

    // eq(10) survived, and so must its two ge thresholds: these need_gevar calls are the
    // discriminating half of the hoist-out check. Had hoist_eq_to_top left them deletable,
    // the forget would have deleted them under the surviving Top eq definition, and
    // re-introducing them here would emit a `red` that the eq definition's clause refutes.
    check(tracker.xliteral_for(w == 10_i) == w10);
    tracker.need_gevar(w, 10_i);
    tracker.need_gevar(w, 11_i);
    logger.emit_rup_proof_line(WPBSum{} + 1_i * (w != 10_i) + 1_i * (w < 11_i) >= 1_i, ProofLevel::Current);
    logger.forget_proof_level(1);

    // ---- u: eviction must take its lines out of the level's bucket, not just delete them ----
    // Evicting the deepest threshold of the chain gives it no upper neighbour and so no
    // stitch, which leaves the evicted chain clause as the last line recorded at level 1.
    // forget_proof_level deletes a bucket's final interval with a trailing bare `del id`
    // (`del range`'s exclusive upper has no negative encoding there) -- and unlike
    // `del range`, `del id` does not skip an already-deleted line but errors on it. So this
    // is the shape in which forgetting a level an eviction has touched rejects the proof
    // unless the eviction dropped its lines from the bucket as well as deleting them.
    logger.enter_proof_level(1);
    tracker.need_gevar(u, 50_i);
    tracker.need_gevar(u, 60_i);
    check(tracker.evict_order_literal(u, 60_i, nullopt));
    logger.forget_proof_level(1);

    // ---- t: an ancestor's definition is not this subtree's to evict ----
    // The window tidies from wherever the search currently stands, which is not necessarily
    // the level that minted the atom. A definition at an ancestor level outlives this
    // subtree, and lines emitted anywhere between that level and here may name it -- only
    // Top references are tracked, so for those intermediate levels there is no pin to
    // consult and "no pin" cannot be read as "unreferenced".
    //
    // This is table_layout's shape, reduced: it retired `rowheight[1] >= 81`, minted at
    // level 4, from level 20, while the objective lower-bound row that named it -- emitted
    // back at level 4 -- stayed live for another 239 backtracks. The re-introduction was
    // then not a re-introduction at all, and its `-> 1` witness could not discharge that
    // still-live row.
    //
    // The level-1 line below is what makes this discriminating rather than decorative: it is
    // a reference that survives the level-2 subtree, so evicting either threshold at level 2
    // strands it, and the `need_gevar` after the forget then re-emits the `red` pair the
    // stranded line refutes.
    //
    // Measured by mutation, stubbing the ancestor rule out fails this test twice over: the
    // two return-value checks below go first (which is what the harness reports, since it
    // runs veripb only on a zero exit), and with those neutered as well the proof itself is
    // rejected -- `Proofgoal ... could not be autoproven`, the same signature, from the same
    // cause, as table_layout at gate 0.
    logger.enter_proof_level(1);
    tracker.need_gevar(t, 30_i);
    tracker.need_gevar(t, 70_i);
    logger.emit_rup_proof_line(WPBSum{} + 1_i * (t < 70_i) + 1_i * (t >= 30_i) >= 1_i, ProofLevel::Current);

    logger.enter_proof_level(2);
    // Standing one level deeper, both thresholds belong to the ancestor: refused.
    check(! tracker.evict_order_literal(t, 30_i, nullopt));
    check(! tracker.evict_order_literal(t, 70_i, nullopt));
    // A definition minted here is this subtree's own, and stays evictable -- the rule must
    // cost the window only what it has to.
    tracker.need_gevar(t, 50_i);
    check(tracker.evict_order_literal(t, 50_i, nullopt));
    logger.forget_proof_level(2);

    // Still live, so no `red` pair is written here -- unless the ancestor rule let level 2
    // take it, in which case this is the re-introduction that strands the line above.
    tracker.need_gevar(t, 70_i);

    // And a threshold this level minted, named by nothing, is still the window's to take:
    // the rule is about ancestry, not a blanket refusal.
    tracker.need_gevar(t, 90_i);
    check(tracker.evict_order_literal(t, 90_i, nullopt));
    logger.forget_proof_level(1);

    // ---- v: a ge threshold pinned only through a pol's operands ----
    // The ge half of the union rule. A `pol` landing at Top over an operand naming
    // `v >= 30` is a permanent reference to that threshold, but nothing in the emitted pol
    // text names it -- the literals are the arithmetic's result -- so before the operand
    // union nothing pinned it and the window was free to take it.
    //
    // Asserted through the Top-pin bookkeeping rather than through the proof, because that
    // is where the difference shows immediately: an unpinned threshold at a positive level
    // is evictable with no cause at all, and a pinned one is evictable only against its
    // sole cause. Checking the proof instead would only fail once something later named the
    // evicted atom.
    logger.enter_proof_level(1);
    tracker.need_gevar(v, 30_i);
    check(tracker.order_literal_is_live(v, 30_i));
    // Deletable right now: this level minted it and nothing names it.
    check(tracker.evict_order_literal(v, 30_i, nullopt));
    tracker.need_gevar(v, 30_i);

    {
        PolBuilder pol;
        pol.add(logger.emit_rup_proof_line(WPBSum{} + 1_i * (v < 30_i) + 1_i * (v >= 30_i) >= 1_i, ProofLevel::Temporary));
        pol.emit(logger, ProofLevel::Top);
    }

    // The Top pol pinned it: a no-cause eviction is now refused, and LineHoist is the cause
    // that owns the pin. Both halves matter -- the first is what fails without the union,
    // the second is what fails if the pin is recorded against the wrong cause.
    check(! tracker.evict_order_literal(v, 30_i, nullopt));
    check(! tracker.evict_order_literal(v, 30_i, Cause::SoliHoist));
    check(tracker.evict_order_literal(v, 30_i, Cause::LineHoist));
    logger.forget_proof_level(1);

    logger.enter_proof_level(0);
    logger.conclude_none();
    tracker.finalise();

    return rc;
}
