/* Merging pairwise at-most-ones into a clique inequality.
 *
 * Nothing here goes near a Cumulative. The routine's whole job is the cutting-
 * planes arithmetic, so it is tested on a micro model of `k` fresh flags whose
 * only constraints are the pairwise at-most-ones --- and that model is
 * *satisfiable* (everything false satisfies every at-most-one), which matters:
 * against an unsatisfiable one every RUP step is vacuously valid and a
 * corrupted derivation would sail through, which is the trap #656 walked into.
 *
 * The four claims made here are separate:
 *
 *   1. the derivation follows, for cliques of two to twelve;
 *   2. the line that comes back is the clique inequality and not something
 *      weaker --- which nothing but the `ia` pin can say *here*, because every
 *      step of a corrupted merge is still individually sound, and this model
 *      has no consumer to reject it downstream;
 *   3. the induction is necessary, which the NaiveOneShot mutation shows by
 *      being accepted for two and three members and rejected from four on;
 *   4. a guard rides through unchanged and comes out with coefficient exactly
 *      `k - 1`, which the guarded contradiction pins down from both sides: too
 *      few copies of the guard-is-false axiom and the pol does not close, too
 *      many and it is not a contradiction the checker will take.
 */

#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/innards/proofs/am1_from_pairs.hh>
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

    enum class Guard
    {
        /// The plain fold: every at-most-one is unconditional.
        None,
        /// Every at-most-one carries an extra disjunct, so the clique
        /// inequality holds only where the guard is false --- min_distance's
        /// shape.
        Present
    };

    auto check(size_t k, Am1FromPairsMutation mutation, Model model_kind, Guard guard_kind, const string & tag, bool expect_veripb_to_accept) -> void
    {
        auto proof_name = "am1_from_pairs_" + to_string(k) + "_" + tag;
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

        std::optional<ProofFlag> guard;
        if (guard_kind == Guard::Present)
            guard = model.create_proof_flag("guard");

        // The lower triangle, in the order the induction consumes it. Labelled,
        // because a pol step may only reference an OPB row by name. A guarded
        // pair is `~a_i + ~a_j + g >= 1`, written here as `a_i + a_j + ~g <= 2`.
        vector<vector<ProofLine>> at_most_ones(k);
        for (size_t j = 1; j < k; ++j)
            for (size_t i = 0; i < j; ++i) {
                WPBSum pair;
                pair += 1_i * flags[i];
                pair += 1_i * flags[j];
                if (guard)
                    pair += 1_i * ! *guard;
                auto bound = guard ? 2_i : 1_i;
                at_most_ones[j].push_back(model.add_labelled_constraint("amo" + to_string(i) + "x" + to_string(j), move(pair) <= bound));
            }

        std::optional<ProofLine> two_active, guard_false;
        if (model_kind == Model::WithTwoActive) {
            WPBSum both;
            both += 1_i * flags[0];
            both += 1_i * flags[1];
            two_active = model.add_labelled_constraint("bothactive", move(both) >= 2_i);
            // A guarded clique inequality says nothing at all where the guard
            // holds, so two active members only contradict it once the guard is
            // ruled out.
            if (guard)
                guard_false = model.add_labelled_constraint("guardfalse", WPBSum{} + 1_i * ! *guard >= 1_i);
        }
        model.finalise();

        ProofLogger logger(proof_options, tracker);
        tracker.switch_from_model_to_proof(&logger);
        logger.start_proof(model);
        tracker.emit_delayed_proof_steps();

        auto clique = recover_am1_from_pairs(
            logger, members, at_most_ones, ProofLevel::Top, guard ? std::optional<ProofLiteralOrFlag>{*guard} : std::nullopt, mutation);

        if (two_active) {
            // The clique inequality says at most one is active and the axiom
            // says two are, so one pol closes it --- and `ia` against the
            // result insists that it really is a contradiction rather than
            // something the checker refuted by other means. The guarded fold
            // carries `k - 1` of the guard, so it takes that many copies of the
            // axiom ruling it out to cancel them.
            PolBuilder contradiction;
            contradiction.add(clique).add(*two_active);
            if (guard_false)
                contradiction.add(*guard_false, Integer{static_cast<long long>(k) - 1});
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
        check(k, am1_from_pairs_mutation::None{}, Model::Plain, Guard::None, "honest", true);
    println(cerr, "cliques of 2 to 12 members: derived and verified");

    // And it means what it says: two members active contradicts it.
    for (size_t k : {2, 3, 5, 8})
        check(k, am1_from_pairs_mutation::None{}, Model::WithTwoActive, Guard::None, "contradiction", true);
    println(cerr, "the clique inequality contradicts two active members");

    // Dropping an input from the last merge. Worth being clear about what this
    // catches: the merge itself stays sound, and lands on a weaker line that
    // VeriPB would be right to accept. It is the `ia` pin that rejects, which
    // is the only reason this mutation is a test at all.
    for (size_t k : {3, 4, 7})
        check(k, am1_from_pairs_mutation::DropAnAtMostOne{}, Model::Plain, Guard::None, "dropped", false);
    println(cerr, "veripb rejected a merge missing an at-most-one, as expected");

    // Claiming no member may be active at all.
    for (size_t k : {2, 3, 6})
        check(k, am1_from_pairs_mutation::ClaimOneMore{}, Model::Plain, Guard::None, "onemore", false);
    println(cerr, "veripb rejected the one-stronger claim, as expected");

    // The induction is necessary, and here is where. Summing every at-most-one
    // and dividing once gives `ceil(k/2)`, which is `k - 1` exactly while
    // `k <= 3`. So the naive derivation is *accepted* for two and three members
    // and rejected from four on --- if this boundary ever moves, the argument
    // for the induction has changed and the comment explaining it is wrong.
    for (size_t k : {2, 3})
        check(k, am1_from_pairs_mutation::NaiveOneShot{}, Model::Plain, Guard::None, "naive", true);
    for (size_t k : {4, 5, 9})
        check(k, am1_from_pairs_mutation::NaiveOneShot{}, Model::Plain, Guard::None, "naive", false);
    println(cerr, "the one-shot merge works to three members and fails from four, as the induction's premise says");

    // Leaving the division off the last merge gives a line that is *stronger*
    // than the clique inequality, and the pin rejects it regardless, because an
    // implication check cannot see an equivalence that needs dividing. Not a
    // corruption to be defended against so much as a property being relied on:
    // it says the final division is load-bearing for the pin and not only for
    // the induction.
    for (size_t k : {3, 5})
        check(k, am1_from_pairs_mutation::SkipFinalDivision{}, Model::Plain, Guard::None, "nodivide", false);
    println(cerr, "veripb rejected an undivided --- and strictly stronger --- last merge, as expected");

    // And the same again with a guard riding through the induction, which is
    // min_distance's shape. The claim being tested is the one the header makes
    // about the coefficient: the guard comes out at exactly `k - 1`, so the pin
    // states it, and the contradiction below cancels it with exactly that many
    // copies of the axiom ruling the guard out. Either number being wrong is a
    // rejection, which is why the contradiction model is the interesting one
    // here rather than an extra.
    for (size_t k = 2; k <= 12; ++k)
        check(k, am1_from_pairs_mutation::None{}, Model::Plain, Guard::Present, "ghonest", true);
    for (size_t k : {2, 3, 5, 8})
        check(k, am1_from_pairs_mutation::None{}, Model::WithTwoActive, Guard::Present, "gcontradiction", true);
    println(cerr, "the guarded fold derives, and carries the guard at k-1 exactly");

    // A guard does not soften the pin: every mutation is still caught, and the
    // one-shot merge still turns from right to wrong between three members and
    // four.
    for (size_t k : {3, 4, 7})
        check(k, am1_from_pairs_mutation::DropAnAtMostOne{}, Model::Plain, Guard::Present, "gdropped", false);
    for (size_t k : {2, 3, 6})
        check(k, am1_from_pairs_mutation::ClaimOneMore{}, Model::Plain, Guard::Present, "gonemore", false);
    for (size_t k : {2, 3})
        check(k, am1_from_pairs_mutation::NaiveOneShot{}, Model::Plain, Guard::Present, "gnaive", true);
    for (size_t k : {4, 5, 9})
        check(k, am1_from_pairs_mutation::NaiveOneShot{}, Model::Plain, Guard::Present, "gnaive", false);
    for (size_t k : {3, 5})
        check(k, am1_from_pairs_mutation::SkipFinalDivision{}, Model::Plain, Guard::Present, "gnodivide", false);
    println(cerr, "the guarded fold rejects every mutation the plain one does");

    return EXIT_SUCCESS;
}
