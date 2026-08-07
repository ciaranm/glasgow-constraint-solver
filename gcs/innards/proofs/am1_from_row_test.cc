/* Recovering a cardinality bound over some of a capacity row's tasks.
 *
 * Nothing here goes near a Cumulative: the routine's whole job is the cutting-
 * planes arithmetic, so it is tested on a micro model whose only constraint is
 * one resource row --- and that model is *satisfiable* (everything false fits
 * under any non-negative capacity), which matters, since against an
 * unsatisfiable one every step is vacuously valid and a corrupted derivation
 * would sail through.
 *
 * The claim worth making loudly is that the pairwise at-most-one is not a
 * separate program but this one at two members, so both sizes are checked here
 * together and the pairwise cases are simply the ones with two demands.
 *
 * The awkward thing this file records is where the mistakes are caught. The
 * bound is weak enough that the arithmetic has slack in every direction:
 * dividing by a divisor one too large, or one too small, or leaving a task in
 * that should have been weakened out, all still land on lines that imply the
 * bound whenever the bound is true, and an `ia` pin accepts them because its
 * check saturates. So a pin says the *conclusion* is right and says nothing at
 * all about how it was reached, and the one failure mode that matters --- a set
 * that does not overshoot the capacity, which is an off-by-one in the caller's
 * conflict test --- cannot be caught in the proof at all. That is why the
 * routine refuses a non-overshooting set outright, and why this file checks the
 * refusal rather than checking what veripb makes of it.
 */

#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/innards/proofs/am1_from_row.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>

#include <cstddef>
#include <cstdlib>
#include <iostream>
#include <set>
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
using std::set;
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
        println(cerr, "am1 from row test failure: {}", message);
        std::exit(EXIT_FAILURE);
    }

    /// Recover the bound over `members` out of a row over `demands`, check it
    /// is the bound the fixture says, pin the line to `sum <= claim`, and say
    /// whether veripb was happy. `demand_offset` corrupts the demand the
    /// routine is told the first member has, leaving the row and the claim
    /// alone.
    auto check(const string & name, const vector<Integer> & demands, Integer capacity, const set<size_t> & members, Integer expected_at_most,
        Integer claim, Integer demand_offset, bool expect_veripb_to_accept) -> void
    {
        auto proof_name = "am1_from_row_" + name;
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

        vector<Integer> member_demands;
        vector<ProofFlag> weaken_out;
        WPBSum claimed;
        for (size_t i = 0; i < demands.size(); ++i) {
            if (members.contains(i)) {
                member_demands.push_back(demands[i] + (member_demands.empty() ? demand_offset : 0_i));
                claimed += 1_i * flags[i];
            }
            else
                weaken_out.push_back(flags[i]);
        }

        auto recovered = recover_am1_from_row(logger, resource, member_demands, weaken_out, capacity, ProofLevel::Top);
        if (demand_offset == 0_i && recovered.at_most != expected_at_most)
            fail(name + ": the routine says at most " + to_string(recovered.at_most.raw_value) + " may run, not the " +
                to_string(expected_at_most.raw_value) + " the fixture claims");

        logger.emit(ImpliesProofRule{recovered.line}, move(claimed) <= claim, ProofLevel::Top);
        logger.conclude_none();
        tracker.finalise();

        auto accepted = run_veripb(proof_name + ".opb", proof_name + ".pbp");
        if (accepted != expect_veripb_to_accept)
            fail(name + ": veripb " + (accepted ? "accepted" : "rejected") + " it, expecting the opposite");
        dispose_of_proof_files(proof_name);
    }

    /// The overshoot guard, which needs no proof: building it is what throws.
    auto check_refused(const string & name, const vector<Integer> & member_demands, Integer capacity) -> void
    {
        auto proof_name = "am1_from_row_refused_" + name;
        ProofOptions proof_options{proof_name};
        NamesAndIDsTracker tracker(proof_options);
        ProofModel model(proof_options, tracker);
        auto u = model.create_proof_flag("u"), v = model.create_proof_flag("v");
        WPBSum load;
        load += 6_i * u;
        load += 4_i * v;
        auto resource = model.add_labelled_constraint("resource", move(load) <= 10_i);
        model.finalise();

        ProofLogger logger(proof_options, tracker);
        tracker.switch_from_model_to_proof(&logger);
        logger.start_proof(model);
        tracker.emit_delayed_proof_steps();

        bool threw = false;
        try {
            [[maybe_unused]] auto got = recover_am1_from_row(logger, resource, member_demands, {}, capacity, ProofLevel::Top);
        }
        catch (const ProofError &) {
            threw = true;
        }

        logger.conclude_none();
        tracker.finalise();
        dispose_of_proof_files(proof_name);

        if (! threw)
            fail(name + ": a set that fits under the capacity was given a bound anyway");
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    // A set that fits, exactly or with room to spare, has no bound to recover,
    // and dividing by zero is not a proof step. This is the failure mode an
    // off-by-one in a caller's conflict test lands on, and the only one that
    // has to be caught here: everything below shows that once the set really
    // does overshoot, the proof survives the arithmetic being wrong.
    check_refused("exact_fit", {6_i, 4_i}, 10_i);
    check_refused("room_to_spare", {6_i, 1_i}, 10_i);
    check_refused("no_members", {}, 10_i);
    println(cerr, "a set that fits is refused rather than given a bound");

    if (! can_run_veripb()) {
        println(cerr, "veripb is not available, so the rest of this test is skipped");
        return EXIT_SUCCESS;
    }

    // Two members: the pairwise at-most-one, which is this program and not
    // another one. The divisor works out to the margin `c_u + c_v - C` on its
    // own, because that margin is at most the larger demand exactly when the
    // smaller one fits under the capacity.
    check("pair_plain", {6_i, 7_i, 3_i, 2_i}, 10_i, {0, 1}, 1_i, 1_i, 0_i, true);
    // Margin of exactly one, with nothing else in the row to hide behind.
    check("pair_margin_one", {6_i, 5_i}, 10_i, {0, 1}, 1_i, 1_i, 0_i, true);
    // A demand *above* the capacity. The task can never run at all, so the
    // at-most-one is a weak thing to say about it --- but the arithmetic does
    // not care, because saturation caps both coefficients at the margin and the
    // division rounds them back up to one. This is the case #548 expected to
    // need a `c_j <= C` side condition for, and it does not: the condition
    // belongs to clique *discovery*, where a task that can never run would
    // otherwise pad every clique it touches.
    check("pair_over_capacity", {1_i, 12_i, 4_i}, 10_i, {1, 2}, 1_i, 1_i, 0_i, true);
    check("pair_both_full", {10_i, 10_i, 1_i}, 10_i, {0, 1}, 1_i, 1_i, 0_i, true);
    println(cerr, "two members give the at-most-one, including over the capacity");

    // Three and more, in one step. Where the members share a row this is what
    // to use instead of recovering every pair and folding them: one `pol`
    // rather than `k(k-1)/2` of them plus an induction over them.
    check("four_sixes", {6_i, 6_i, 6_i, 6_i}, 10_i, {0, 1, 2, 3}, 1_i, 1_i, 0_i, true);
    check("two_sixes_a_nine", {6_i, 6_i, 9_i}, 10_i, {0, 1, 2}, 1_i, 1_i, 0_i, true);
    // Unbalanced demands push the divisor up until the clique condition fails:
    // `Delta = 17` is not more than `d(|K| - 2) = 18`, so this lands on `<= 2`
    // and an at-most-one has to be reached the long way round. A caller that
    // assumed the bound rather than reading it would claim one here and be
    // wrong, which is what the second of these says.
    check("unbalanced", {9_i, 6_i, 6_i, 6_i}, 10_i, {0, 1, 2, 3}, 2_i, 2_i, 0_i, true);
    check("unbalanced_overclaimed", {9_i, 6_i, 6_i, 6_i}, 10_i, {0, 1, 2, 3}, 2_i, 1_i, 0_i, false);
    // And with no conflicting pair at all --- 4 + 4 fits under 10 --- the same
    // chain still yields a cardinality cut, which nothing built out of pairwise
    // at-most-ones could ever produce.
    check("no_conflicting_pair", {4_i, 4_i, 4_i}, 10_i, {0, 1, 2}, 2_i, 2_i, 0_i, true);
    println(cerr, "three and more give the clique inequality where the demands allow, and a cardinality cut otherwise");

    // The slack, recorded because a caller needs to know it is there. A demand
    // reported either side of the truth still pins: too large and the division
    // rounds the coefficients up, leaving a line the pin's own saturation
    // recovers the bound from; too small and the degree rounds up instead,
    // giving a line that is stronger than the bound and implies it outright. So
    // no mutation of this arithmetic is a test of it, and a caller that wants
    // its own conclusion checked has to pin that conclusion rather than
    // trusting these lines to be what they look like.
    check("demand_too_large", {6_i, 7_i, 3_i}, 10_i, {0, 1}, 1_i, 1_i, 1_i, true);
    check("demand_too_small", {6_i, 7_i, 3_i}, 10_i, {0, 1}, 1_i, 1_i, -1_i, true);
    println(cerr, "a demand off by one either way still pins, so the pin is about the claim and not the route");

    return EXIT_SUCCESS;
}
