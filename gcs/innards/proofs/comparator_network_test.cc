/* Proof-only comparator networks over bit-encoded integer wires.
 *
 * Two tests, at the component's two layers.
 *
 * The first goes nowhere near a schedule. A comparator's whole job is to say,
 * in cutting planes, what muxing two wires on a selector does to them, so it is
 * tested on a micro model with no constraints at all, into which two wires are
 * pinned to constants and one comparator is run. The model being *satisfiable*
 * is the point, and the trap #656 walked into: against an unsatisfiable one
 * every RUP step is vacuously valid and a corrupted derivation sails through.
 * Here the only way to reach a contradiction is to pin a claim the comparator's
 * own rows refute, which is what each `Claim` below does.
 *
 * The second is the whole construction: a disjunctive instance whose tasks
 * cannot fit in their window, encoded pairwise --- `before` flags and one
 * separation clause per pair, nothing time-indexed anywhere --- and refuted by
 * sorting the tasks inside the proof and telescoping. That model *is*
 * unsatisfiable, so a green run says only that the arithmetic went through; the
 * mutations are what say it had to. Each corrupts one step and must be
 * rejected, and one control asks for the same proof over a window the tasks do
 * fit in, where the endgame has to fail.
 */

#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/innards/proofs/comparator_network.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>

#include <algorithm>
#include <bit>
#include <cstdlib>
#include <iostream>
#include <map>
#include <string>
#include <utility>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using std::cerr;
using std::map;
using std::move;
using std::pair;
using std::string;
using std::to_string;
using std::vector;
using std::ranges::max;
using std::ranges::min;

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

    auto check_comparator(int a_value, int b_value, Claim claim, const string & tag, bool expect_accepted) -> void
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

        ComparatorNetwork network(logger, 4, 0_i, 15_i, ProofLevel::Top);
        auto a = network.fresh_wire("a"), b = network.fresh_wire("b");
        network.pin(a, Integer{a_value});
        network.pin(b, Integer{b_value});
        // A comparator permutes whole tasks, so both inputs need a duration
        // before there is anything to compare. What it is does not matter here.
        network.add_task(a, 1_i);
        network.add_task(b, 1_i);
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

    /* The pairwise disjunctive encoding, and nothing else: this is the model a
     * Disjunctive already defines, written out here over *real* integer
     * variables so that the network meets the shapes it will meet in a
     * propagator --- bits it does not own, widths that differ from task to
     * task, and a reification big-M chosen by the model rather than by the
     * proof.
     */
    struct PairwiseModel
    {
        vector<SimpleIntegerVariableID> starts;
        map<pair<size_t, size_t>, ProofFlag> before;
        map<pair<size_t, size_t>, ProofLine> before_rows;
        map<pair<size_t, size_t>, ProofLine> separation_clauses;
        map<pair<size_t, size_t>, Integer> guard_coefficients;
        int width = 0;
    };

    auto build_pairwise_model(ProofModel & model, NamesAndIDsTracker & tracker, const vector<int> & durations, int window_lo, int window_hi)
        -> PairwiseModel
    {
        auto tasks = durations.size();
        PairwiseModel built;

        // Each start is encoded to its own width, from its own domain: a task
        // that must finish by the window's end cannot start after
        // `window_hi - duration`, so a long task gets a narrower encoding than
        // a short one, and the network has to pad.
        for (size_t i = 0; i < tasks; ++i) {
            SimpleIntegerVariableID start{i};
            model.set_up_integer_variable(start, Integer{window_lo}, Integer{window_hi - durations[i]}, "s" + to_string(i), std::nullopt);
            built.starts.push_back(start);
        }
        built.width = static_cast<int>(std::bit_width(static_cast<unsigned long long>(window_hi)));

        for (size_t i = 0; i < tasks; ++i)
            for (size_t j = 0; j < tasks; ++j) {
                if (i == j)
                    continue;
                auto flag = model.create_proof_flag("b" + to_string(i) + "_" + to_string(j));
                built.before.emplace(pair{i, j}, flag);

                // before_ij <-> start_i + duration_i <= start_j, exactly as
                // Disjunctive::define_proof_model writes it. The [r] half is
                // what the network consumes, and its big-M is whatever the
                // reifier picked --- which the network then has to raise to its
                // own, so ask rather than assume.
                auto ineq = WPBSum{} + 1_i * built.starts[i] + -1_i * built.starts[j] <= Integer{-durations[i]};
                built.guard_coefficients.emplace(pair{i, j}, -tracker.reification_shape(ineq, HalfReifyOnConjunctionOf{{flag}}).reif_coefficient);
                built.before_rows.emplace(pair{i, j}, model.add_two_way_reified_constraint(ineq, flag).first);
            }

        for (size_t i = 0; i < tasks; ++i)
            for (size_t j = i + 1; j < tasks; ++j) {
                WPBSum clause;
                clause += 1_i * built.before.at(pair{i, j});
                clause += 1_i * built.before.at(pair{j, i});
                built.separation_clauses.emplace(
                    pair{i, j}, model.add_labelled_constraint("sep" + to_string(i) + "_" + to_string(j), move(clause) >= 1_i));
            }

        return built;
    }

    auto check_refutation(const vector<int> & durations, int window_lo, int window_hi, ComparatorNetworkMutation mutation, const string & tag,
        bool expect_accepted) -> void
    {
        auto proof_name = "comparator_network_refute_" + to_string(durations.size()) + "_" + tag;
        ProofOptions proof_options{proof_name};
        NamesAndIDsTracker tracker(proof_options);
        ProofModel model(proof_options, tracker);
        auto built = build_pairwise_model(model, tracker, durations, window_lo, window_hi);
        model.finalise();

        ProofLogger logger(proof_options, tracker);
        tracker.switch_from_model_to_proof(&logger);
        logger.start_proof(model);
        tracker.emit_delayed_proof_steps();

        ComparatorNetwork network(logger, built.width, Integer{window_lo}, Integer{window_hi}, ProofLevel::Top, mutation);

        vector<ProofWire> tasks;
        for (size_t i = 0; i < durations.size(); ++i) {
            // A wire straight over the model variable's own bits. Nothing is
            // copied and nothing is emitted: the network reads the encoding
            // that is already there, and pads the narrow ones itself.
            vector<ProofLiteralOrFlag> bits;
            for (Integer b = 0_i; b < tracker.num_bits(built.starts[i]); ++b)
                bits.push_back(ProofBitVariable{built.starts[i], b, true});
            tasks.push_back(network.wire_over(bits));
        }

        for (size_t i = 0; i < durations.size(); ++i) {
            network.add_task(tasks[i], Integer{durations[i]});
            // The window's own bounds, as a propagator would have them: not
            // model rows but facts about the state, which here RUP straight
            // from the variables' domains.
            network.set_upper_bound(
                tasks[i], logger.emit_rup_proof_line(WPBSum{} + 1_i * built.starts[i] <= Integer{window_hi - durations[i]}, ProofLevel::Top));
            network.set_lower_bound(tasks[i], logger.emit_rup_proof_line(WPBSum{} + 1_i * built.starts[i] >= Integer{window_lo}, ProofLevel::Top));
        }

        auto direction = [&](size_t i, size_t j) {
            return ModelSeparation{built.before.at(pair{i, j}), built.before_rows.at(pair{i, j}), built.guard_coefficients.at(pair{i, j})};
        };
        for (size_t i = 0; i < durations.size(); ++i)
            for (size_t j = i + 1; j < durations.size(); ++j)
                network.add_separation(tasks[i], direction(i, j), tasks[j], direction(j, i), built.separation_clauses.at(pair{i, j}));

        auto sorted = network.sort(tasks);
        // The window-energy row. It is contradictory exactly when the tasks do
        // not fit, so concluding is one RUP away --- and when a mutation has
        // left the sum short, or when the control's window is wide enough, that
        // RUP is where the proof falls over.
        (void)network.sum_up(sorted);
        logger.conclude_unsatisfiable(false);
        tracker.finalise();

        auto accepted = run_veripb(proof_name + ".opb", proof_name + ".pbp");
        if (accepted != expect_accepted)
            fail("refutation of " + to_string(durations.size()) + " tasks in [" + to_string(window_lo) + ", " + to_string(window_hi) + ") (" + tag +
                "): veripb " + (accepted ? "accepted" : "rejected") + " where it should have done the opposite");
        dispose_of_proof_files(proof_name);
    }

    /// Unequal durations, and the total work they carry: a window one unit
    /// narrower than that is unsatisfiable by a margin of one, so every
    /// separation clause matters.
    auto tight_instance(size_t tasks) -> pair<vector<int>, int>
    {
        vector<int> durations;
        for (size_t i = 0; i < tasks; ++i)
            durations.push_back(2 + static_cast<int>((i * 5 + 3) % 7));
        auto total = 0;
        for (auto d : durations)
            total += d;
        return {durations, total};
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
            check_comparator(a, b, Claim::Nothing, "plain", true);
            check_comparator(a, b, Claim::TheTruth, "truth", true);
            // The two that say the rows have content: claiming the low output
            // is not the smaller input, or the high one not the larger, has to
            // fail --- and does so by the RUP not going through, which is what
            // a false claim against sound rows looks like.
            check_comparator(a, b, Claim::LoIsNotTheSmaller, "lo_wrong", false);
            check_comparator(a, b, Claim::HiIsNotTheLarger, "hi_wrong", false);
        }

    // A window that starts where the time line does, and one slid along it.
    // The offset one is what a propagator's window actually looks like, and is
    // where the earliest task's lower bound stops being free: from zero a bit
    // vector cannot be negative and the endgame gets that end for nothing.
    const auto offset = 7;
    for (size_t tasks = 3; tasks <= 8; ++tasks) {
        auto [durations, work] = tight_instance(tasks);
        check_refutation(durations, 0, work - 1, comparator_network_mutation::None{}, "honest", true);
        check_refutation(durations, offset, offset + work - 1, comparator_network_mutation::None{}, "offset", true);
        // The same tasks with one more unit of window: they fit, and the
        // endgame must not close. This is the control that says the refutation
        // is about the instance rather than about the scaffolding.
        check_refutation(durations, 0, work, comparator_network_mutation::None{}, "roomy", false);
        check_refutation(durations, offset, offset + work, comparator_network_mutation::None{}, "offset_roomy", false);
    }

    {
        auto [durations, work] = tight_instance(4);
        auto lo = offset, hi = offset + work - 1;
        check_refutation(durations, lo, hi, comparator_network_mutation::DropPositivity{}, "drop_positivity", false);
        check_refutation(durations, lo, hi, comparator_network_mutation::SwapDurations{}, "swap_durations", false);
        check_refutation(durations, lo, hi, comparator_network_mutation::RupGap{}, "rup_gap", false);
        // Accepted, and expected to be: with every duration pinned, propagation
        // reaches a muxed duration's positivity without the case split. Asserted
        // so that it is on the record, and so that it starts failing the day
        // durations stop being constants.
        check_refutation(durations, lo, hi, comparator_network_mutation::RupPositivity{}, "rup_positivity", true);
        check_refutation(durations, lo, hi, comparator_network_mutation::RupPreservation{}, "rup_preservation", false);
        check_refutation(durations, lo, hi, comparator_network_mutation::DropPreservation{}, "drop_preservation", false);
    }

    return EXIT_SUCCESS;
}
