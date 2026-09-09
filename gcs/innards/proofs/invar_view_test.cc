#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>

#include <optional>
#include <variant>

using namespace gcs;
using namespace gcs::innards;

using std::get_if;
using std::nullopt;

// Range ("in") literals on a registered view, at the tracker level: see
// dev_docs/view-range-literals.md.
//
// What this covers, and it is deliberately narrow:
//
//   - need_pol_item_defining_literal's InRange / NotInRange arms on a view. The
//     constraint suite cannot reach these at all -- every caller of that function
//     today passes a bound or an equality -- so without this they are untested.
//   - the sign arithmetic of interval_on_underlying / interval_on_view, for both view
//     signs and both signs of offset, and in both directions of the mirror. This is
//     checked with find_xliteral_for, which does not introduce what it cannot find:
//     ask for an interval on one side, and the other side's literal must exist at
//     exactly the mapped bounds and not at the neighbouring ones.
//
// What it does NOT cover, and must not be read as covering: whether the link
// clauses are necessary. Those are P2 clauses in the sense of
// dev_docs/range_literals_spec.md §1, and a RUP check is strictly stronger than the
// single unit-propagation pass they exist to support -- so every line below still
// verifies with the link pair deleted. That was checked, not assumed. The witnesses
// for the links are range_witness_w6 through w9, which fail on a backtrack clause.
auto main() -> int
{
    ProofOptions proof_options{"invar_view_test"};

    NamesAndIDsTracker tracker(proof_options);
    ProofModel model(proof_options, tracker);
    // need_view only works while the model is being written, and the tracker only
    // knows a model is being written once it has been handed one (Proof does this).
    tracker.start_writing_model(&model);

    // Two underlying variables, so that both view signs can be exercised. The bounds
    // are wide enough for the intervals below to sit strictly inside them, which is
    // the case that needs the links -- one abutting a bound would cross anyway,
    // through the bound axiom, and prove nothing.
    SimpleIntegerVariableID x{0}, y{1};
    model.set_up_integer_variable(x, 0_i, 30_i, "x", nullopt);
    model.set_up_integer_variable(y, 0_i, 30_i, "y", nullopt);

    // A positive view and a negated one, with offsets of either sign.
    ViewOfIntegerVariableID pos{x, false, 17_i}; // pos = x + 17,  in [17, 47]
    ViewOfIntegerVariableID neg{y, true, -7_i};  // neg = -y - 7,  in [-37, -7]
    auto pos_id = tracker.need_view(pos);
    auto neg_id = tracker.need_view(neg);

    model.finalise();

    ProofLogger logger(proof_options, tracker);
    tracker.switch_from_model_to_proof(&logger);
    logger.start_proof(model);
    tracker.emit_delayed_proof_steps();

    int rc = 0;
    // The mirror's arithmetic, which is the substance of this test. Ask for an interval
    // on one side only, then check with a *non-creating* lookup that the other side's
    // literal exists at exactly the mapped bounds, and that the neighbouring
    // off-by-one intervals do not. find_xliteral_for is the lookup that does not
    // introduce what it fails to find, which is what makes this a test rather than a
    // request.
    auto exists = [&](const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> & cond) { return tracker.find_xliteral_for(cond).has_value(); };

    // pos = x + 17, so [30, 34] on the view is [13, 17] on x.
    static_cast<void>(tracker.need_invar(pos_id, 30_i, 34_i));
    if (! exists(in_range(SimpleOrProofOnlyIntegerVariableID{x}, 13_i, 17_i)))
        rc = 1;
    if (exists(in_range(SimpleOrProofOnlyIntegerVariableID{x}, 14_i, 18_i)) || exists(in_range(SimpleOrProofOnlyIntegerVariableID{x}, 12_i, 16_i)))
        rc = 1;

    // neg = -y - 7, so [10, 14] on y is [-21, -17] on the view: the endpoints swap and
    // the offset is negative, which is the arithmetic most likely to be wrong. Asked
    // from the underlying side this time, so the other direction of the map is covered.
    static_cast<void>(tracker.need_invar(y, 10_i, 14_i));
    if (! exists(in_range(SimpleOrProofOnlyIntegerVariableID{neg_id}, -21_i, -17_i)))
        rc = 1;
    if (exists(in_range(SimpleOrProofOnlyIntegerVariableID{neg_id}, -24_i, -20_i)) ||
        exists(in_range(SimpleOrProofOnlyIntegerVariableID{neg_id}, -20_i, -16_i)))
        rc = 1;

    // need_pol_item_defining_literal on a view's range condition: the InRange arm must
    // give the forward reification row and the NotInRange arm the reverse one, the same
    // way round as for a plain variable, and both must be real proof lines rather than
    // bare literals.
    auto pol_line = [&](const IntegerVariableCondition & cond) -> std::optional<ProofLine> {
        auto item = tracker.need_pol_item_defining_literal(cond);
        if (auto * line = get_if<ProofLine>(&item))
            return *line;
        return nullopt;
    };
    auto in_line = pol_line(in_range(IntegerVariableID{pos}, 30_i, 34_i));
    auto notin_line = pol_line(not_in_range(IntegerVariableID{pos}, 30_i, 34_i));
    if (! in_line || ! notin_line || *in_line == *notin_line)
        rc = 1;

    // The same for the negated view, whose literal was created from the other side.
    auto neg_in_line = pol_line(in_range(IntegerVariableID{neg}, -21_i, -17_i));
    auto neg_notin_line = pol_line(not_in_range(IntegerVariableID{neg}, -21_i, -17_i));
    if (! neg_in_line || ! neg_notin_line || *neg_in_line == *neg_notin_line)
        rc = 1;

    // The four crossings, as RUP lines. These check the *arithmetic*: a wrong endpoint
    // map makes the line unprovable and the test fails. They do not check that the
    // link clauses are needed -- see the note at the top. Stated over the public
    // conditions, so they also check that a view's range condition resolves to the
    // view's own literal rather than being deviewed onto the underlying variable.
    auto rup = [&](const WPBSumLE & ineq) { static_cast<void>(logger.emit_rup_proof_line(ineq, ProofLevel::Top)); };

    rup(WPBSum{} + 1_i * ! in_range(IntegerVariableID{pos}, 30_i, 34_i) + 1_i * in_range(IntegerVariableID{x}, 13_i, 17_i) >= 1_i);
    rup(WPBSum{} + 1_i * ! in_range(IntegerVariableID{x}, 13_i, 17_i) + 1_i * in_range(IntegerVariableID{pos}, 30_i, 34_i) >= 1_i);
    rup(WPBSum{} + 1_i * ! in_range(IntegerVariableID{neg}, -21_i, -17_i) + 1_i * in_range(IntegerVariableID{y}, 10_i, 14_i) >= 1_i);
    rup(WPBSum{} + 1_i * ! in_range(IntegerVariableID{y}, 10_i, 14_i) + 1_i * in_range(IntegerVariableID{neg}, -21_i, -17_i) >= 1_i);

    // A width-1 interval is the eq atom on both sides, so it needs no interval link and
    // must not make one: the eq links already carry it.
    if (tracker.need_invar(pos_id, 25_i, 25_i) != ProofLiteral{ProofVariableCondition{pos_id, VariableConditionOperator::Equal, 25_i}})
        rc = 1;
    rup(WPBSum{} + 1_i * (IntegerVariableID{pos} != 25_i) + 1_i * (IntegerVariableID{x} == 8_i) >= 1_i);

    logger.conclude_none();
    tracker.finalise();
    return rc;
}
