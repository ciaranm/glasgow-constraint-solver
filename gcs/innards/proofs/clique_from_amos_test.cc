/* Merging pairwise at-most-ones into a clique inequality.
 *
 * Nothing here goes near a Cumulative. The routine's whole job is the cutting-
 * planes arithmetic, so it is tested on a micro model of `k` fresh flags whose
 * only constraints are the pairwise at-most-ones --- and that model is
 * *satisfiable* (everything false satisfies every at-most-one), which matters:
 * against an unsatisfiable one every RUP step is vacuously valid and a
 * corrupted derivation would sail through, which is the trap #656 walked into.
 *
 * The three claims made here are separate:
 *
 *   1. the derivation follows, for cliques of two to twelve;
 *   2. the line that comes back is the clique inequality and not something
 *      weaker --- which nothing but the `ia` pin can say, because every step of
 *      a corrupted merge is still individually sound;
 *   3. the induction is necessary, which the NaiveOneShot mutation shows by
 *      being accepted for two and three members and rejected from four on.
 */

#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/innards/proofs/clique_from_amos.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>

#include <cstddef>
#include <cstdlib>
#include <iostream>
#include <optional>
#include <string>
#include <utility>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#include <fmt/ranges.h>
#endif

using std::cerr;
using std::move;
using std::size_t;
using std::string;
using std::to_string;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::println;
#else
using fmt::println;
#endif

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::test_innards;

namespace
{
    auto fail(const string & message) -> void
    {
        println(cerr, "clique from amos test failure: {}", message);
        std::exit(EXIT_FAILURE);
    }

    enum class Model
    {
        /// The at-most-ones alone: satisfiable, so every step has to stand up
        /// on its own.
        Plain,
        /// Plus an axiom forcing two members active, which the clique
        /// inequality must contradict.
        WithTwoActive
    };

    auto check(size_t k, CliqueMutation mutation, Model model_kind, const string & tag, bool expect_veripb_to_accept) -> void
    {
        auto proof_name = "clique_from_amos_" + to_string(k) + "_" + tag;
        ProofOptions proof_options{proof_name};
        NamesAndIDsTracker tracker(proof_options);
        ProofModel model(proof_options, tracker);

        vector<ProofFlag> flags;
        vector<ProofLiteralOrFlag> members;
        for (size_t i = 0; i < k; ++i) {
            auto flag = model.create_proof_flag("member" + to_string(i));
            flags.push_back(flag);
            members.push_back(flag);
        }

        // The lower triangle, in the order the induction consumes it. Labelled,
        // because a pol step may only reference an OPB row by name.
        vector<vector<ProofLine>> at_most_ones(k);
        for (size_t j = 1; j < k; ++j)
            for (size_t i = 0; i < j; ++i) {
                WPBSum pair;
                pair += 1_i * flags[i];
                pair += 1_i * flags[j];
                at_most_ones[j].push_back(model.add_labelled_constraint("amo" + to_string(i) + "x" + to_string(j), move(pair) <= 1_i));
            }

        std::optional<ProofLine> two_active;
        if (model_kind == Model::WithTwoActive) {
            WPBSum both;
            both += 1_i * flags[0];
            both += 1_i * flags[1];
            two_active = model.add_labelled_constraint("bothactive", move(both) >= 2_i);
        }
        model.finalise();

        ProofLogger logger(proof_options, tracker);
        tracker.switch_from_model_to_proof(&logger);
        logger.start_proof(model);
        tracker.emit_delayed_proof_steps();

        auto clique = derive_clique_from_amos(logger, members, at_most_ones, ProofLevel::Top, mutation);

        if (two_active) {
            // The clique inequality says at most one is active and the axiom
            // says two are, so one pol closes it --- and `ia` against the
            // result insists that it really is a contradiction rather than
            // something the checker refuted by other means.
            PolBuilder contradiction;
            contradiction.add(clique).add(*two_active);
            auto combined = contradiction.emit(logger, ProofLevel::Top);
            logger.emit(ImpliesProofRule{combined}, WPBSum{} >= 1_i, ProofLevel::Top);
            logger.conclude_unsatisfiable(false);
        }
        else
            logger.conclude_none();

        tracker.finalise();

        auto accepted = run_veripb(proof_name + ".opb", proof_name + ".pbp");
        if (accepted != expect_veripb_to_accept) {
            if (accepted)
                fail("k=" + to_string(k) + " (" + tag +
                    "): veripb accepted a proof built from a deliberately corrupted derivation, so the honest one has slack in it");
            else
                fail("k=" + to_string(k) + " (" + tag + "): veripb rejected an honest proof");
        }
        dispose_of_proof_files(proof_name);
    }

    /* The at-most-ones this routine consumes have to come from somewhere, and
     * for #548 they come from a resource constraint `sum c_i x_i <= C`: two
     * tasks whose demands together exceed the capacity cannot both run. The
     * recipe is weaken the others out, saturate, divide by the margin.
     *
     * Checked here rather than argued, because two things about it are only
     * decidable by running it: whether the derivation needs `c_u, c_v <= C`
     * (the arithmetic suggests not, since division rounds coefficients up), and
     * whether a pair that fits *exactly* is correctly refused.
     */
    auto check_pair_at_most_one(
        const string & name, const vector<Integer> & demands, Integer capacity, size_t u, size_t v, bool expect_veripb_to_accept) -> void
    {
        auto proof_name = "clique_from_amos_pair_" + name;
        ProofOptions proof_options{proof_name};
        NamesAndIDsTracker tracker(proof_options);
        ProofModel model(proof_options, tracker);

        vector<ProofFlag> flags;
        WPBSum load;
        for (size_t i = 0; i < demands.size(); ++i) {
            flags.push_back(model.create_proof_flag("task" + to_string(i)));
            load += demands[i] * flags[i];
        }
        auto resource = model.add_labelled_constraint("resource", WPBSum{load} <= capacity);
        model.finalise();

        ProofLogger logger(proof_options, tracker);
        tracker.switch_from_model_to_proof(&logger);
        logger.start_proof(model);
        tracker.emit_delayed_proof_steps();

        // Weakening drops a term and takes its coefficient off the degree, so
        // what is left after dropping everything but the pair is exactly the
        // margin by which the two overshoot.
        auto margin = demands[u] + demands[v] - capacity;
        PolBuilder pair;
        pair.add(resource);
        for (size_t i = 0; i < demands.size(); ++i)
            if (i != u && i != v)
                pair.weaken(flags[i], tracker);
        pair.saturate();
        // A pair that fits exactly has a margin of zero and no at-most-one to
        // derive. Dividing by one keeps the step legal so that the claim below
        // is what fails, which is the point of running the case at all.
        pair.divide_by(margin > 0_i ? margin : 1_i);
        auto derived = pair.emit(logger, ProofLevel::Top);

        WPBSum both;
        both += 1_i * flags[u];
        both += 1_i * flags[v];
        logger.emit(ImpliesProofRule{derived}, move(both) <= 1_i, ProofLevel::Top);
        logger.conclude_none();
        tracker.finalise();

        auto accepted = run_veripb(proof_name + ".opb", proof_name + ".pbp");
        if (accepted != expect_veripb_to_accept)
            fail("pair at-most-one (" + name + "): veripb " + (accepted ? "accepted" : "rejected") + " it, expecting the opposite");
        dispose_of_proof_files(proof_name);
    }

    /* When several members of a clique draw their conflicts from the SAME
     * resource row, the pairwise at-most-ones are not the cheapest premises to
     * work from --- the row itself is stronger than the edges it implies, and
     * the same weaken/saturate/divide chain lands on the whole sub-clique
     * inequality in one step, skipping both the pairwise derivations and the
     * induction over them.
     *
     * With `Delta = sum_{K} c_i - C` and `d = min(c_max, Delta)`, dividing
     * gives `sum_{K} ~a_i >= ceil(Delta / d)`, which is `|K| - 1` exactly when
     * `Delta > d * (|K| - 2)`. Recorded here as a checked fact rather than an
     * argument, because it is what should decide how #548's certificate is
     * built and it is worth knowing where the condition stops holding.
     *
     * The same chain with a smaller `ceil(Delta / d)` is a *cardinality* cut
     * --- `sum a_i <= |K| - ceil(Delta/d)` --- which is valid for sets with no
     * conflicting pair at all, and which the pairwise machinery cannot see.
     */
    auto check_row_gives_clique(
        const string & name, const vector<Integer> & demands, Integer capacity, Integer expected_at_most, bool expect_veripb_to_accept) -> void
    {
        auto proof_name = "clique_from_amos_row_" + name;
        ProofOptions proof_options{proof_name};
        NamesAndIDsTracker tracker(proof_options);
        ProofModel model(proof_options, tracker);

        vector<ProofFlag> flags;
        WPBSum load, all;
        auto total = 0_i, largest = 0_i;
        for (size_t i = 0; i < demands.size(); ++i) {
            flags.push_back(model.create_proof_flag("task" + to_string(i)));
            load += demands[i] * flags[i];
            all += 1_i * flags[i];
            total += demands[i];
            largest = largest > demands[i] ? largest : demands[i];
        }
        auto resource = model.add_labelled_constraint("resource", WPBSum{load} <= capacity);
        model.finalise();

        ProofLogger logger(proof_options, tracker);
        tracker.switch_from_model_to_proof(&logger);
        logger.start_proof(model);
        tracker.emit_delayed_proof_steps();

        auto delta = total - capacity;
        auto divisor = largest < delta ? largest : delta;
        PolBuilder chain;
        chain.add(resource).saturate().divide_by(divisor);
        auto derived = chain.emit(logger, ProofLevel::Top);

        logger.emit(ImpliesProofRule{derived}, move(all) <= expected_at_most, ProofLevel::Top);
        logger.conclude_none();
        tracker.finalise();

        auto accepted = run_veripb(proof_name + ".opb", proof_name + ".pbp");
        if (accepted != expect_veripb_to_accept)
            fail("row-to-clique (" + name + "): veripb " + (accepted ? "accepted" : "rejected") + " it, expecting the opposite");
        dispose_of_proof_files(proof_name);
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    if (! can_run_veripb()) {
        println(cerr, "veripb is not available, and this test is entirely about what it accepts");
        return EXIT_SUCCESS;
    }

    // The derivation follows, over the whole range the callers will use. Twelve
    // is where #548 expects to stop caring: the merge is O(k^2) additions per
    // time point, so a clique is not something to be casual about.
    for (size_t k = 2; k <= 12; ++k)
        check(k, clique_mutation::None{}, Model::Plain, "honest", true);
    println(cerr, "cliques of 2 to 12 members: derived and verified");

    // And it means what it says: two members active contradicts it.
    for (size_t k : {2, 3, 5, 8})
        check(k, clique_mutation::None{}, Model::WithTwoActive, "contradiction", true);
    println(cerr, "the clique inequality contradicts two active members");

    // Dropping an input from the last merge. Worth being clear about what this
    // catches: the merge itself stays sound, and lands on a weaker line that
    // VeriPB would be right to accept. It is the `ia` pin that rejects, which
    // is the only reason this mutation is a test at all.
    for (size_t k : {3, 4, 7})
        check(k, clique_mutation::DropAnAtMostOne{}, Model::Plain, "dropped", false);
    println(cerr, "veripb rejected a merge missing an at-most-one, as expected");

    // Claiming no member may be active at all.
    for (size_t k : {2, 3, 6})
        check(k, clique_mutation::ClaimOneMore{}, Model::Plain, "onemore", false);
    println(cerr, "veripb rejected the one-stronger claim, as expected");

    // The induction is necessary, and here is where. Summing every at-most-one
    // and dividing once gives `ceil(k/2)`, which is `k - 1` exactly while
    // `k <= 3`. So the naive derivation is *accepted* for two and three members
    // and rejected from four on --- if this boundary ever moves, the argument
    // for the induction has changed and the comment explaining it is wrong.
    for (size_t k : {2, 3})
        check(k, clique_mutation::NaiveOneShot{}, Model::Plain, "naive", true);
    for (size_t k : {4, 5, 9})
        check(k, clique_mutation::NaiveOneShot{}, Model::Plain, "naive", false);
    println(cerr, "the one-shot merge works to three members and fails from four, as the induction's premise says");

    // Where the at-most-ones come from: weaken, saturate, divide by the margin.
    check_pair_at_most_one("plain", {6_i, 7_i, 3_i, 2_i}, 10_i, 0, 1, true);
    // Margin of exactly one, with nothing else in the row to hide behind.
    check_pair_at_most_one("margin_one", {6_i, 5_i}, 10_i, 0, 1, true);
    // A demand *above* the capacity. The task can never run at all, so the
    // at-most-one is a weak thing to say about it --- but the derivation does
    // not care, because saturation caps both coefficients at the margin and the
    // division rounds them back up to one. This is the case #548 expects to
    // need a `c_j <= C` side condition for, and it does not: the condition
    // belongs to clique *discovery*, where a task that can never run would
    // otherwise pad every clique it touches.
    check_pair_at_most_one("over_capacity", {1_i, 12_i, 4_i}, 10_i, 0, 1, true);
    check_pair_at_most_one("both_full", {10_i, 10_i, 1_i}, 10_i, 0, 1, true);
    // And the camouflage case: a pair summing to *exactly* the capacity fits,
    // so there is no at-most-one, and veripb says so. An off-by-one in the
    // conflict test lands here.
    check_pair_at_most_one("fits_exactly", {6_i, 4_i, 3_i}, 10_i, 0, 1, false);
    println(cerr, "pair at-most-ones: derived over the capacity, and refused for a pair that fits exactly");

    // Leaving the division off the last merge gives a line that is *stronger*
    // than the clique inequality, and the pin rejects it regardless, because an
    // implication check cannot see an equivalence that needs dividing. Not a
    // corruption to be defended against so much as a property being relied on:
    // it says the final division is load-bearing for the pin and not only for
    // the induction.
    for (size_t k : {3, 5})
        check(k, clique_mutation::SkipFinalDivision{}, Model::Plain, "nodivide", false);
    println(cerr, "veripb rejected an undivided --- and strictly stronger --- last merge, as expected");

    // The same chain applied to a whole resource row at once, which is what
    // #548 should be doing wherever a row covers three or more clique members.
    check_row_gives_clique("four_sixes", {6_i, 6_i, 6_i, 6_i}, 10_i, 1_i, true);
    check_row_gives_clique("two_sixes_a_nine", {6_i, 6_i, 9_i}, 10_i, 1_i, true);
    // Unbalanced demands push `d` up until the condition fails: Delta = 17 is
    // not more than d(|K| - 2) = 18, so the one-shot lands on `<= 2` and the
    // clique inequality has to be reached the long way round.
    check_row_gives_clique("unbalanced", {9_i, 6_i, 6_i, 6_i}, 10_i, 1_i, false);
    check_row_gives_clique("unbalanced_weaker", {9_i, 6_i, 6_i, 6_i}, 10_i, 2_i, true);
    // And with no conflicting pair at all --- 4 + 4 fits under 10 --- the same
    // chain still yields a cardinality cut, which nothing built out of pairwise
    // at-most-ones could ever produce.
    check_row_gives_clique("no_conflicting_pair", {4_i, 4_i, 4_i}, 10_i, 2_i, true);
    println(cerr, "a shared resource row gives its sub-clique in one step, and a cardinality cut where no pair conflicts");

    return EXIT_SUCCESS;
}
