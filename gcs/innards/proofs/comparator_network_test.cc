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

        ComparatorNetwork network(logger, 4, 15_i, ProofLevel::Top);
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
     * Disjunctive already defines, written out here over plain proof flags so
     * that the test owns every big-M and the network is exercised against the
     * shapes it will meet rather than against rows invented to suit it.
     */
    struct PairwiseModel
    {
        vector<vector<ProofFlag>> start_bits;
        vector<ProofLine> upper_bounds;
        map<pair<size_t, size_t>, ProofFlag> before;
        map<pair<size_t, size_t>, ProofLine> before_rows;
        map<pair<size_t, size_t>, ProofLine> separation_clauses;
        Integer big = 0_i;
        int width = 0;
    };

    auto build_pairwise_model(ProofModel & model, const vector<int> & durations, int horizon) -> PairwiseModel
    {
        auto tasks = durations.size();
        PairwiseModel built;
        // Every start gets the same width, which its own bound row then
        // narrows: a shared width is what lets the network's wires all be read
        // the same way, and costs nothing but a spare high bit.
        auto widest_start = horizon - min(durations);
        auto widest = widest_start > max(durations) ? widest_start : max(durations);
        built.width = static_cast<int>(std::bit_width(static_cast<unsigned long long>(widest)));
        built.big = Integer{horizon};

        built.start_bits.resize(tasks);
        for (size_t i = 0; i < tasks; ++i)
            for (auto t = 0; t < built.width; ++t)
                built.start_bits[i].push_back(model.create_proof_flag("x" + to_string(i) + "_" + to_string(t)));

        auto start = [&](size_t i, Integer sign) {
            WPBSum sum;
            for (auto t = 0; t < built.width; ++t)
                sum += (sign * Integer{1LL << t}) * built.start_bits[i][t];
            return sum;
        };

        // `start_i <= horizon - duration_i`. Load-bearing in a way it is not
        // with equal durations: the shared width lets a start range over more
        // than its own window, and this is the row that says it may not.
        for (size_t i = 0; i < tasks; ++i)
            built.upper_bounds.push_back(model.add_labelled_constraint("ub" + to_string(i), start(i, 1_i) <= Integer{horizon - durations[i]}));

        for (size_t i = 0; i < tasks; ++i)
            for (size_t j = 0; j < tasks; ++j) {
                if (i == j)
                    continue;
                auto name = "b" + to_string(i) + "_" + to_string(j);
                auto flag = model.create_proof_flag(name);
                built.before.emplace(pair{i, j}, flag);

                // [r] before_ij -> start_j - start_i >= duration_i
                auto forward = start(j, 1_i);
                for (auto & term : start(i, -1_i).terms)
                    forward += term;
                forward += built.big * ! flag;
                built.before_rows.emplace(pair{i, j}, model.add_labelled_constraint(name + "r", move(forward) >= Integer{durations[i]}));

                // [f] ~before_ij -> start_i - start_j >= 1 - duration_i
                auto reverse = start(i, 1_i);
                for (auto & term : start(j, -1_i).terms)
                    reverse += term;
                reverse += (built.big + 1_i) * flag;
                model.add_labelled_constraint(name + "f", move(reverse) >= Integer{1 - durations[i]});
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

    auto check_refutation(const vector<int> & durations, int horizon, ComparatorNetworkMutation mutation, const string & tag, bool expect_accepted)
        -> void
    {
        auto proof_name = "comparator_network_refute_" + to_string(durations.size()) + "_" + tag;
        ProofOptions proof_options{proof_name};
        NamesAndIDsTracker tracker(proof_options);
        ProofModel model(proof_options, tracker);
        auto built = build_pairwise_model(model, durations, horizon);
        model.finalise();

        ProofLogger logger(proof_options, tracker);
        tracker.switch_from_model_to_proof(&logger);
        logger.start_proof(model);
        tracker.emit_delayed_proof_steps();

        ComparatorNetwork network(logger, built.width, Integer{horizon}, ProofLevel::Top, mutation);

        vector<ProofWire> tasks;
        for (size_t i = 0; i < durations.size(); ++i)
            tasks.push_back(network.wire_over(built.start_bits[i]));
        for (size_t i = 0; i < durations.size(); ++i) {
            network.add_task(tasks[i], Integer{durations[i]});
            network.set_upper_bound(tasks[i], built.upper_bounds[i]);
        }
        for (size_t i = 0; i < durations.size(); ++i)
            for (size_t j = i + 1; j < durations.size(); ++j)
                network.add_separation(tasks[i], built.before.at(pair{i, j}), built.before_rows.at(pair{i, j}), tasks[j], built.before.at(pair{j, i}),
                    built.before_rows.at(pair{j, i}), built.separation_clauses.at(pair{i, j}), built.big);

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
            fail("refutation of " + to_string(durations.size()) + " tasks in " + to_string(horizon) + " (" + tag + "): veripb " +
                (accepted ? "accepted" : "rejected") + " where it should have done the opposite");
        dispose_of_proof_files(proof_name);
    }

    /// Unequal durations that overload the window by exactly one unit, so the
    /// instance is unsatisfiable by a margin of one and every separation clause
    /// matters.
    auto tight_instance(size_t tasks) -> pair<vector<int>, int>
    {
        vector<int> durations;
        for (size_t i = 0; i < tasks; ++i)
            durations.push_back(2 + static_cast<int>((i * 5 + 3) % 7));
        auto total = 0;
        for (auto d : durations)
            total += d;
        return {durations, total - 1};
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

    for (size_t tasks = 3; tasks <= 8; ++tasks) {
        auto [durations, horizon] = tight_instance(tasks);
        check_refutation(durations, horizon, comparator_network_mutation::None{}, "honest", true);
        // Same tasks, one more unit of window: they fit, and the endgame must
        // not close. This is the control that says the refutation is about the
        // instance rather than about the scaffolding.
        check_refutation(durations, horizon + 1, comparator_network_mutation::None{}, "roomy", false);
    }

    {
        auto [durations, horizon] = tight_instance(4);
        check_refutation(durations, horizon, comparator_network_mutation::DropPositivity{}, "drop_positivity", false);
        check_refutation(durations, horizon, comparator_network_mutation::SwapDurations{}, "swap_durations", false);
        check_refutation(durations, horizon, comparator_network_mutation::RupGap{}, "rup_gap", false);
        // Accepted, and expected to be: with every duration pinned, propagation
        // reaches a muxed duration's positivity without the case split. Asserted
        // so that it is on the record, and so that it starts failing the day
        // durations stop being constants.
        check_refutation(durations, horizon, comparator_network_mutation::RupPositivity{}, "rup_positivity", true);
        check_refutation(durations, horizon, comparator_network_mutation::RupPreservation{}, "rup_preservation", false);
        check_refutation(durations, horizon, comparator_network_mutation::DropPreservation{}, "drop_preservation", false);
    }

    return EXIT_SUCCESS;
}
