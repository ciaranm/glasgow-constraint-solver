#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>

#include <optional>
#include <variant>

using namespace gcs;
using namespace gcs::innards;

using std::get_if;
using std::nullopt;

// Regression for issue #559. A real (state) {0,1} variable takes the
// direct-only single-bit encoding, so its eq/ne atoms are primitive bit
// literals: id == 1 and id != 0 are the bit eqvar, id == 0 and id != 1 are
// ~eqvar. For such a primitive atom the pol item that
// need_pol_item_defining_literal returns (and that add_for_literal would push
// as a term) must be the atom's own literal, i.e. xliteral_for(atom). Before
// the fix, track_eqvar stored value 1's (eqvar, ~eqvar) pair for value 0 as
// well, so need_pol_item_defining_literal(id == 0) returned eqvar where
// id == 0 is ~eqvar -- the opposite polarity -- silently corrupting any pol
// that cited the value-0 eq/ne atom.
auto main() -> int
{
    ProofOptions proof_options{"eqvar_polarity_test"};

    NamesAndIDsTracker tracker(proof_options);
    ProofModel model(proof_options, tracker);

    SimpleIntegerVariableID x{0};
    model.set_up_integer_variable(x, 0_i, 1_i, "x", nullopt);

    model.finalise();

    ProofLogger logger(proof_options, tracker);
    tracker.switch_from_model_to_proof(&logger);
    logger.start_proof(model);
    tracker.emit_delayed_proof_steps();

    // The pol-defining item of each aliased eq/ne atom must be a raw XLiteral
    // equal to that atom's own literal.
    auto consistent = [&](const VariableConditionFrom<SimpleIntegerVariableID> & cond) -> bool {
        auto item = tracker.need_pol_item_defining_literal(cond);
        auto * xlit = get_if<XLiteral>(&item);
        return xlit && *xlit == tracker.xliteral_for(cond);
    };

    int rc = 0;
    if (! consistent(x == 0_i))
        rc = 1;
    if (! consistent(x == 1_i))
        rc = 1;
    if (! consistent(x != 0_i))
        rc = 1;
    if (! consistent(x != 1_i))
        rc = 1;

    logger.conclude_none();
    tracker.finalise();

    return rc;
}
