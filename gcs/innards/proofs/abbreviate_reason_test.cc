/* Abbreviating a reason to one extension variable.
 *
 * Under a ProofLogger::AbbreviateReason, a temporary line written under the
 * guarded reason names one flag in its place, defined as the conjunction of the
 * reason's literals at the same temporary level. These micro models check the
 * cases that the constraints which opt in do not reach: a hinted RUP whose hint
 * needs the reason's literals set, which works only because the definition is
 * cited ahead of it; a level forgotten while the guard is still alive, after
 * which the flag has to be defined afresh; the size below which nothing is
 * abbreviated; and a claim that is false, which must still be refused once it
 * is abbreviated.
 */

#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>

#include <cstddef>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using std::cerr;
using std::ifstream;
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
        println(cerr, "abbreviate reason test failure: {}", message);
        std::exit(EXIT_FAILURE);
    }

    enum class Shape
    {
        Once,          ///< one guarded line, then the inference at the current level
        AfterForget,   ///< the temporary level is forgotten mid-guard, then used again
        TooSmall,      ///< a reason too short to be worth a definition
        ClaimTooStrong ///< the row needs one more literal than the reason gives
    };

    auto count_definitions(const string & proof_name) -> size_t
    {
        ifstream in{proof_name + ".pbp"};
        size_t result = 0;
        for (string line; getline(in, line);)
            if (line.starts_with("red ") && line.contains("[r]"))
                ++result;
        return result;
    }

    /* Flags a_0 .. a_{n-1} and z, and one row saying that all of the a imply
     * z. The reason is the first `reason_size` of the a. The guarded line claims
     * z under the reason, citing only the row, which propagates only once every
     * a is set: under the abbreviation the line says `~flag` instead, so nothing
     * but the definition, cited first, sets them.
     */
    auto check(const string & name, Shape shape, size_t row_size, size_t reason_size, size_t expected_definitions, const VeripbVerdict & expected)
        -> void
    {
        auto proof_name = "abbreviate_reason_" + name;
        ProofOptions proof_options{proof_name};
        NamesAndIDsTracker tracker(proof_options);
        ProofModel model(proof_options, tracker);

        vector<ProofFlag> a;
        for (size_t i = 0; i < row_size; ++i)
            a.push_back(model.create_proof_flag("a" + to_string(i)));
        auto z = model.create_proof_flag("z");
        WPBSum all_imply_z = WPBSum{} + -1_i * z;
        for (const auto & f : a)
            all_imply_z += 1_i * f;
        auto row = model.add_labelled_constraint("row", move(all_imply_z) <= Integer(static_cast<long long>(row_size)) - 1_i);
        model.finalise();

        ProofLogger logger(proof_options, tracker);
        tracker.switch_from_model_to_proof(&logger);
        logger.start_proof(model);
        tracker.emit_delayed_proof_steps();

        ReasonLiterals reason;
        for (size_t i = 0; i < reason_size; ++i)
            reason.push_back(a[i]);

        auto t = logger.temporary_proof_level();
        {
            ProofLogger::AbbreviateReason abbreviate{logger, reason};
            auto guarded = [&]() {
                logger.emit_under_reason(RUPProofRule{vector<ProofLine>{row}}, WPBSum{} + 1_i * z >= 1_i, ProofLevel::Temporary, reason);
            };
            guarded();
            if (shape == Shape::AfterForget) {
                logger.forget_proof_level(t);
                guarded();
            }
            // The inference itself keeps the whole reason, and follows from the
            // guarded line through the definition's other half.
            logger.emit_under_reason(RUPProofRule{}, WPBSum{} + 1_i * z >= 1_i, ProofLevel::Current, reason);
        }
        logger.forget_proof_level(t);
        logger.conclude_none();
        tracker.finalise();

        if (auto definitions = count_definitions(proof_name); definitions != expected_definitions)
            fail(name + ": expected " + to_string(expected_definitions) + " definition lines, found " + to_string(definitions));
        if (auto problem = veripb_verdict_differs(proof_name, expected))
            fail(name + ": " + *problem);
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

    // Two definition lines, forward and reverse. The hinted line verifies only
    // with the forward line cited ahead of the row.
    check("once", Shape::Once, 5, 5, 2, VeripbAccepts{});

    // Forgetting the level deletes the definition, so the next guarded line
    // needs a second one, under a new name.
    check("after_forget", Shape::AfterForget, 5, 5, 4, VeripbAccepts{});

    // Below the size floor nothing is defined, and the line is written in full.
    check("too_small", Shape::TooSmall, 3, 3, 0, VeripbAccepts{});

    // A reason one literal short of what the row needs: the abbreviated line
    // is false, and must still be refused.
    check("claim_too_strong", Shape::ClaimTooStrong, 6, 5, 2, VeripbRejects{GCS_VERIPB_REJECTS_RUP});

    println(cerr, "abbreviated reasons: verified where the reason suffices, refused where it does not");
    return EXIT_SUCCESS;
}
