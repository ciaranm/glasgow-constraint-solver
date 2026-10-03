#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>

#include <string>

using namespace gcs;
using namespace gcs::innards;

using std::string;

// A trivially true row whose coefficients sum to just under 2^63 but whose
// normalised degree is so negative that the sum less the degree is past 2^63.
// VeriPB 3.0.2 handles such a row in 64-bit arithmetic, the slack overflows,
// and it reports a solution that leaves the row satisfiable as conflicting
// with it. The row writer gives such a row a normalised degree of zero instead
// (emit_inequality_to.cc), so the solution line here must verify. This is the
// row from the original report, over a proof-only variable spanning 61 bits
// and two flags with coefficients near 2^61.
auto main() -> int
{
    ProofOptions proof_options{"row_slack_test"};

    NamesAndIDsTracker tracker(proof_options);
    ProofModel model(proof_options, tracker);

    auto x = model.create_proof_only_integer_variable(Integer{-(1LL << 60)}, Integer{(1LL << 60) - 1}, "x", IntegerVariableProofRepresentation::Bits);
    auto sel = model.create_proof_flag("sel");
    auto eqa = model.create_proof_flag("eqa");

    const Integer k{3458764513820540927LL};
    model.add_constraint(WPBSum{} + -1_i * x + k * ! sel + k * eqa >= Integer{-5764607523034234877LL});
    // As in the original, the literal with the big coefficient is false: it
    // was an equality on a view that cannot take the value.
    model.add_constraint(WPBSum{} + 1_i * ! eqa >= 1_i);

    model.finalise();

    ProofLogger logger(proof_options, tracker);
    tracker.switch_from_model_to_proof(&logger);
    logger.start_proof(model);
    tracker.emit_delayed_proof_steps();

    // Set only x's sign bit and sel, with eqa propagated false. The row still
    // holds whatever the rest are, so the solution check must pass.
    string sign_bit;
    for (const auto & [value, bit] : tracker.each_bit(x))
        if (value < 0_i)
            sign_bit = tracker.pb_file_string_for(bit);
    logger.emit_proof_line("sol " + sign_bit + " " + tracker.pb_file_string_for(sel) + " ;", ProofLevel::Current);

    logger.conclude_none();
    tracker.finalise();

    return 0;
}
