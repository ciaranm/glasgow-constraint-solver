#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>

#include <fstream>
#include <iostream>
#include <optional>
#include <string>

using namespace gcs;
using namespace gcs::innards;

using std::nullopt;
using std::string;

// Range ("in") literals asked for while the model is being written (#310), at the
// tracker level: see need_invar and define_invar_in_model.
//
// What this covers: such a literal's *definition* goes in the OPB, as a labelled
// pair of rows, once however often it is asked for; nothing that *links* it goes
// there, and in particular its view counterpart does not exist until the proof
// starts; once the proof has started, emit_delayed_proof_steps has linked it,
// mirror included -- even across a view registered after the literal was defined,
// which is the ordering that made the request wait for the rest of the delayed
// steps.
//
// What it does NOT cover: whether that linking is needed. As for invar_view_test,
// every line below would verify without it; the witness is range_witness_w10.
auto main() -> int
{
    ProofOptions proof_options{"invar_model_test"};

    NamesAndIDsTracker tracker(proof_options);
    ProofModel model(proof_options, tracker);
    tracker.start_writing_model(&model);

    SimpleIntegerVariableID x{0};
    model.set_up_integer_variable(x, 0_i, 30_i, "x", nullopt);
    SimpleOrProofOnlyIntegerVariableID x_id{x};

    auto exists = [&](const VariableConditionFrom<SimpleOrProofOnlyIntegerVariableID> & cond) { return tracker.find_xliteral_for(cond).has_value(); };

    int rc = 0;

    // A literal on x first, asked for twice, and only then a view of x, so that the
    // view is registered after the literal it will be mirrored from.
    auto first = tracker.need_invar(x, 3_i, 5_i);
    if (tracker.need_invar(x, 3_i, 5_i) != first)
        rc = 1;

    ViewOfIntegerVariableID pos{x, false, 17_i}; // pos = x + 17, in [17, 47]
    auto pos_id = tracker.need_view(pos);
    SimpleOrProofOnlyIntegerVariableID pos_key{pos_id};

    // And one on the view's own variable. pos = x + 17, so [30, 34] on the view is
    // [13, 17] on x, and x's [3, 5] is the view's [20, 22].
    static_cast<void>(tracker.need_invar(pos_id, 30_i, 34_i));

    // Mirroring is linking, so neither counterpart exists while the model is open.
    if (exists(in_range(x_id, 13_i, 17_i)) || exists(in_range(pos_key, 20_i, 22_i))) {
        std::cerr << "a range literal was mirrored while the model was being written\n";
        rc = 1;
    }

    model.finalise();

    ProofLogger logger(proof_options, tracker);
    tracker.switch_from_model_to_proof(&logger);
    logger.start_proof(model);
    tracker.emit_delayed_proof_steps();

    if (! exists(in_range(x_id, 13_i, 17_i)) || ! exists(in_range(pos_key, 20_i, 22_i))) {
        std::cerr << "a range literal the OPB defines was not mirrored at proof start\n";
        rc = 1;
    }

    // The crossings, as RUP lines, both ways for both literals.
    auto rup = [&](const WPBSumLE & ineq) { static_cast<void>(logger.emit_rup_proof_line(ineq, ProofLevel::Top)); };
    rup(WPBSum{} + 1_i * ! in_range(IntegerVariableID{pos}, 30_i, 34_i) + 1_i * in_range(IntegerVariableID{x}, 13_i, 17_i) >= 1_i);
    rup(WPBSum{} + 1_i * ! in_range(IntegerVariableID{x}, 13_i, 17_i) + 1_i * in_range(IntegerVariableID{pos}, 30_i, 34_i) >= 1_i);
    rup(WPBSum{} + 1_i * ! in_range(IntegerVariableID{x}, 3_i, 5_i) + 1_i * in_range(IntegerVariableID{pos}, 20_i, 22_i) >= 1_i);
    rup(WPBSum{} + 1_i * ! in_range(IntegerVariableID{pos}, 20_i, 22_i) + 1_i * in_range(IntegerVariableID{x}, 3_i, 5_i) >= 1_i);

    logger.conclude_none();
    tracker.finalise();

    // Read back: each model-phase literal is defined by exactly its two labelled rows,
    // and neither mirror is in the OPB at all.
    std::ifstream opb{proof_options.proof_file_names.opb_file};
    if (! opb) {
        std::cerr << "could not read back " << proof_options.proof_file_names.opb_file << "\n";
        return 1;
    }
    int x_rows = 0, view_rows = 0, mirror_rows = 0;
    for (string line; std::getline(opb, line);) {
        if (line.starts_with("@i[x][in3_5][r] ") || line.starts_with("@i[x][in3_5][f] "))
            ++x_rows;
        if (line.starts_with("@po[") && (line.contains("][in30_34][r] ") || line.contains("][in30_34][f] ")))
            ++view_rows;
        if (line.contains("[in13_17]") || line.contains("[in20_22]"))
            ++mirror_rows;
    }
    if (x_rows != 2 || view_rows != 2 || mirror_rows != 0) {
        std::cerr << "expected 2 OPB rows defining [x in 3..5], 2 defining [pos in 30..34] and none mentioning a mirror, got " << x_rows << ", "
                  << view_rows << " and " << mirror_rows << "\n";
        rc = 1;
    }

    return rc;
}
