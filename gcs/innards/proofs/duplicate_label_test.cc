#include <gcs/constraint_id.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>

#include <string>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#endif

using namespace gcs;
using namespace gcs::innards;

using std::string;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

// Issue #604: a label is how a proof step cites an OPB row, so no two rows in the
// c[id][role] namespace may carry the same one -- a duplicate makes both uncitable,
// and opbdiff --match-labels pairs the two encoders' rows by label. ProofModel
// rejects the second row rather than picking a winner.
//
// Both overloads a constraint can reach are covered here, because they emit
// independently: the single-inequality one, and the equality one, whose two halves
// are claimed together so that a colliding pair leaves no LE row behind and so that
// the same role passed twice is caught.
//
// Distinct roles must still be accepted, and the .opb left behind must still be
// well-formed with every surviving row citable -- a rejected row must not leave a
// half-written line in the file. The pol steps at the end are what pin that; VeriPB
// fails the test if any label is missing or its row malformed.
namespace
{
    auto expect_throw(const string & what, auto && f) -> bool
    {
        try {
            f();
        }
        catch (const ProofError &) {
            return true;
        }
        print(stderr, "{} was accepted\n", what);
        return false;
    }
}

auto main() -> int
{
    ProofOptions proof_options{"duplicate_label_test"};

    NamesAndIDsTracker tracker(proof_options);
    ProofModel model(proof_options, tracker);

    ConstraintID id{NumberedConstraint{1}};
    auto x = model.create_proof_only_integer_variable(0_i, 10_i, "x", IntegerVariableProofRepresentation::Bits);

    // Distinct roles: accepted.
    model.add_labelled_constraint(id, "first", WPBSum{} + 1_i * x <= 5_i);
    model.add_labelled_constraint(id, "second", WPBSum{} + 1_i * x <= 6_i);
    model.add_labelled_constraint(id, "eqle", "eqge", WPBSum{} + 1_i * x == 4_i);

    auto ok = true;

    // The same role again, naming a genuinely different row: rejected.
    ok &= expect_throw("a second row under role 'first'", [&] { model.add_labelled_constraint(id, "first", WPBSum{} + 1_i * x <= 7_i); });

    // The equality overload emits its two halves itself rather than delegating, so
    // it needs its own claim: a half colliding with an earlier row must be caught
    // there too, whichever half it is.
    ok &= expect_throw(
        "an equality whose LE half reuses role 'eqle'", [&] { model.add_labelled_constraint(id, "eqle", "freshge", WPBSum{} + 1_i * x == 3_i); });
    ok &= expect_throw(
        "an equality whose GE half reuses role 'second'", [&] { model.add_labelled_constraint(id, "freshle", "second", WPBSum{} + 1_i * x == 3_i); });

    // Both halves under one role: the pair collides with itself.
    ok &= expect_throw("an equality using role 'samesame' for both halves",
        [&] { model.add_labelled_constraint(id, "samesame", "samesame", WPBSum{} + 1_i * x == 2_i); });

    // A different constraint may reuse a role: the id is part of the label.
    model.add_labelled_constraint(ConstraintID{NumberedConstraint{2}}, "first", WPBSum{} + 1_i * x <= 8_i);

    model.finalise();

    ProofLogger logger(proof_options, tracker);
    tracker.switch_from_model_to_proof(&logger);
    logger.start_proof(model);
    tracker.emit_delayed_proof_steps();

    // Every accepted row is still there and still citable. A rejected row must not
    // have left a partial line behind, or these fail to parse.
    for (const auto & label : {"c[_1][first]", "c[_1][second]", "c[_1][eqle]", "c[_1][eqge]", "c[_2][first]"})
        logger.emit_proof_line("pol @" + string{label} + " ;", ProofLevel::Current);

    logger.conclude_none();
    tracker.finalise();

    return ok ? 0 : 1;
}
