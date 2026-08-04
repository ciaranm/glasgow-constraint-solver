/* Bridging one constraint's flags to another's.
 *
 * The whole point is that this costs one `pol` and knows nothing about what the
 * flags mean: two flags fully reified on the same inequality cancel it away
 * between them. So the tests are micro models with a couple of integer
 * variables and flags reified over them, and what is checked is that veripb
 * accepts the bridge, that the bridge really does force what it claims, and
 * that flags reified on *different* conditions are not bridgeable --- which is
 * the failure mode, since nothing in the API can tell the two cases apart.
 */

#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/innards/proofs/flag_bridge.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <string>
#include <tuple>
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
using std::string;
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
        println(cerr, "flag bridge test failure: {}", message);
        std::exit(EXIT_FAILURE);
    }

    /* Two flags reified on `start <= t`, as two separate constraints would
     * write them, bridged. `shift` offsets the second flag's condition, so a
     * positive shift makes the target weaker (and the implication true) and a
     * negative one makes it stronger (and the implication false).
     */
    auto check_same_condition(const string & name, Integer t, Integer shift, bool expect_veripb_to_accept) -> void
    {
        auto proof_name = "flag_bridge_same_" + name;
        ProofOptions proof_options{proof_name};
        NamesAndIDsTracker tracker(proof_options);
        ProofModel model(proof_options, tracker);

        SimpleIntegerVariableID start{0};
        model.set_up_integer_variable(start, 0_i, 10_i, "start", std::nullopt);
        auto from = model.create_proof_flag_fully_reifying("from", WPBSum{} + 1_i * start <= t);
        auto to = model.create_proof_flag_fully_reifying("to", WPBSum{} + 1_i * start <= t + shift);
        model.finalise();

        ProofLogger logger(proof_options, tracker);
        tracker.switch_from_model_to_proof(&logger);
        logger.start_proof(model);
        tracker.emit_delayed_proof_steps();

        auto bridge = recover_flag_bridge(logger, from, to, ProofLevel::Top);

        // And it says what it is for: `from` implies `to`. Pinned, because a
        // pol that landed somewhere weaker would otherwise pass unnoticed ---
        // the same reason every other derivation in this directory pins.
        logger.emit(ImpliesProofRule{bridge}, WPBSum{} + 1_i * ! from + 1_i * to >= 1_i, ProofLevel::Top);
        logger.conclude_none();
        tracker.finalise();

        auto accepted = run_veripb(proof_name + ".opb", proof_name + ".pbp");
        if (accepted != expect_veripb_to_accept)
            fail("same-condition bridge (" + name + "): veripb " + (accepted ? "accepted" : "rejected") + " it, expecting the opposite");
        dispose_of_proof_files(proof_name);
    }

    /* Cumulative's shape: `active <-> before /\ after`, written twice over the
     * same start variable as two posted constraints would, and bridged. This is
     * the one an inferred constraint over several resources actually needs.
     */
    auto check_conjunction(const string & name, Integer length, Integer other_length, bool expect_veripb_to_accept) -> void
    {
        auto proof_name = "flag_bridge_conj_" + name;
        ProofOptions proof_options{proof_name};
        NamesAndIDsTracker tracker(proof_options);
        ProofModel model(proof_options, tracker);

        const auto t = 4_i;
        SimpleIntegerVariableID start{0};
        model.set_up_integer_variable(start, 0_i, 10_i, "start", std::nullopt);

        auto make = [&](const string & side, Integer p) {
            auto before = model.create_proof_flag_fully_reifying(side + "before", WPBSum{} + 1_i * start <= t);
            auto after = model.create_proof_flag_fully_reifying(side + "after", WPBSum{} + -1_i * start <= -(t - p + 1_i));
            auto active = model.create_proof_flag_fully_reifying(side + "active", WPBSum{} + -1_i * before + -1_i * after <= -2_i);
            return std::tuple{before, after, active};
        };

        auto [from_before, from_after, from_active] = make("from", length);
        auto [to_before, to_after, to_active] = make("to", other_length);
        model.finalise();

        ProofLogger logger(proof_options, tracker);
        tracker.switch_from_model_to_proof(&logger);
        logger.start_proof(model);
        tracker.emit_delayed_proof_steps();

        auto bridge =
            recover_conjunction_flag_bridge(logger, from_active, {from_before, from_after}, to_active, {to_before, to_after}, ProofLevel::Top);

        logger.emit(ImpliesProofRule{bridge}, WPBSum{} + 1_i * ! from_active + 1_i * to_active >= 1_i, ProofLevel::Top);
        logger.conclude_none();
        tracker.finalise();

        auto accepted = run_veripb(proof_name + ".opb", proof_name + ".pbp");
        if (accepted != expect_veripb_to_accept)
            fail("conjunction bridge (" + name + "): veripb " + (accepted ? "accepted" : "rejected") + " it, expecting the opposite");
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

    check_same_condition("identical", 4_i, 0_i, true);
    // A `to` reified one unit *weaker* bridges too, and should: `start <= 4`
    // really does imply `start <= 5`. Worth pinning down, because it says the
    // routine is not doing a syntactic equality check on the conditions --- it
    // is doing the arithmetic, and the arithmetic is what decides.
    check_same_condition("weaker_target", 4_i, 1_i, true);
    // One unit *stronger* is a false implication, and the cancellation leaves
    // nothing to saturate into a clause. This is the direction a caller can get
    // wrong, and nothing but running it says so.
    check_same_condition("stronger_target", 4_i, -1_i, false);
    println(cerr, "flag bridges: derived where the implication holds, refused where it does not");

    check_conjunction("identical", 3_i, 3_i, true);
    // Two resources cannot disagree about a task's duration, but if the caller
    // ever pairs up the wrong tasks that is what it looks like from here: `to`'s
    // `after` is then the stronger condition and the conjunct bridge fails.
    check_conjunction("shorter_target", 3_i, 2_i, false);
    println(cerr, "conjunction bridges: derived for matching conjuncts, refused for mismatched ones");

    return EXIT_SUCCESS;
}
