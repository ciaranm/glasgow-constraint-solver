/* Proof-only comparator networks over bit-encoded integer wires.
 *
 * Nothing here goes near a Disjunctive. The component's whole job is to
 * introduce wires that exist only inside a proof and to say, in cutting
 * planes, what a comparator does to them --- so it is tested on a micro model
 * with no constraints at all, into which two wires are pinned to constants and
 * a comparator is run.
 *
 * The model being *satisfiable* is the point, and the trap #656 walked into:
 * against an unsatisfiable one every RUP step is vacuously valid and a
 * corrupted derivation sails through. Here the only way to reach a
 * contradiction is to pin a claim the comparator's own rows refute, which is
 * what each `Claim` below does.
 *
 * Three things are checked, for every ordered pair of small values:
 *
 *   1. the wires and the comparator are introduced without VeriPB objecting,
 *      which is a statement about the redundance witnesses rather than about
 *      the arithmetic;
 *   2. `lo` really is the smaller input and `hi` the larger --- claiming
 *      otherwise is refuted;
 *   3. claiming what is *true* of them is not refuted, so the rows are not
 *      simply contradictory.
 */

#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/innards/proofs/comparator_network.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>

#include <cstdlib>
#include <iostream>
#include <string>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using std::cerr;
using std::move;
using std::string;
using std::to_string;

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
        println(cerr, "comparator network test failure: {}", message);
        std::exit(EXIT_FAILURE);
    }

    enum class Claim
    {
        /// Introduce the wires and the comparator and stop. Must verify, and
        /// says nothing beyond "the reds are well formed".
        Nothing,
        /// `lo >= a + 1` where a is the smaller input: false, so the record
        /// rows must refute it.
        LoIsNotTheSmaller,
        /// `hi + 1 <= b` where b is the larger input: false likewise.
        HiIsNotTheLarger,
        /// `lo <= a` and `hi >= b`, which are true: must NOT be refuted, or
        /// the comparator's rows are contradictory and prove anything.
        TheTruth
    };

    auto check(int a_value, int b_value, Claim claim, const string & tag, bool expect_accepted) -> void
    {
        auto proof_name = "comparator_network_" + to_string(a_value) + "_" + to_string(b_value) + "_" + tag;
        ProofOptions proof_options{proof_name};
        NamesAndIDsTracker tracker(proof_options);
        ProofModel model(proof_options, tracker);
        // A model with no constraints: everything below is a conservative
        // extension of nothing, so a contradiction can only come from the
        // claim under test.
        model.finalise();

        ProofLogger logger(proof_options, tracker);
        tracker.switch_from_model_to_proof(&logger);
        logger.start_proof(model);
        tracker.emit_delayed_proof_steps();

        ComparatorNetwork network(logger, 4, ProofLevel::Top);
        auto a = network.fresh_wire("a"), b = network.fresh_wire("b");
        network.pin(a, Integer{a_value});
        network.pin(b, Integer{b_value});
        auto c = network.compare(a, b, "c");

        auto smaller = a_value <= b_value ? a : b;
        auto larger = a_value <= b_value ? b : a;

        auto claim_row = [&](WPBSum sum, Integer rhs) { logger.emit_rup_proof_line(move(sum) >= rhs, ProofLevel::Top); };

        switch (claim) {
        case Claim::Nothing: break;
        case Claim::LoIsNotTheSmaller: {
            WPBSum claim_sum;
            network.add_terms(claim_sum, c.lo, 1_i);
            network.add_terms(claim_sum, smaller, -1_i);
            claim_row(move(claim_sum), 1_i);
        } break;
        case Claim::HiIsNotTheLarger: {
            WPBSum claim_sum;
            network.add_terms(claim_sum, larger, 1_i);
            network.add_terms(claim_sum, c.hi, -1_i);
            claim_row(move(claim_sum), 1_i);
        } break;
        case Claim::TheTruth: {
            WPBSum lo_claim;
            network.add_terms(lo_claim, smaller, 1_i);
            network.add_terms(lo_claim, c.lo, -1_i);
            claim_row(move(lo_claim), 0_i);
            WPBSum hi_claim;
            network.add_terms(hi_claim, c.hi, 1_i);
            network.add_terms(hi_claim, larger, -1_i);
            claim_row(move(hi_claim), 0_i);
        } break;
        }
        logger.conclude_none();
        tracker.finalise();

        auto accepted = run_veripb(proof_name + ".opb", proof_name + ".pbp");
        if (accepted != expect_accepted)
            fail("a=" + to_string(a_value) + " b=" + to_string(b_value) + " (" + tag + "): veripb " + (accepted ? "accepted" : "rejected") +
                " where it should have done the opposite");
        dispose_of_proof_files(proof_name);
    }
}

auto main(int, char *[]) -> int
{
    if (! can_run_veripb()) {
        println(cerr, "veripb not found, skipping");
        return EXIT_SUCCESS;
    }

    for (auto a = 0; a < 6; ++a)
        for (auto b = 0; b < 6; ++b) {
            check(a, b, Claim::Nothing, "plain", true);
            check(a, b, Claim::TheTruth, "truth", true);
            // The two that say the rows have content: claiming the low output
            // is not the smaller input, or the high one not the larger, has to
            // fail --- and does so by the RUP not going through, which is what
            // a false claim against sound rows looks like.
            check(a, b, Claim::LoIsNotTheSmaller, "lo_wrong", false);
            check(a, b, Claim::HiIsNotTheLarger, "hi_wrong", false);
        }

    return EXIT_SUCCESS;
}
