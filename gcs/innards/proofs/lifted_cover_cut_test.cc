/* Deriving a lifted cover cut from a capacity row.
 *
 * Nothing here goes near a Cumulative: the routine's whole job is to turn a
 * knapsack dynamic programme into a proof, so it is tested on a micro model
 * whose only constraint is one resource row --- and that model is
 * *satisfiable* (everything false fits under any non-negative capacity), which
 * matters, since against an unsatisfiable one every step is vacuously valid and
 * a corrupted derivation would sail through.
 *
 * Two things are being checked, and they are checked by different means.
 *
 * The first is that the dynamic programme decides validity exactly: it is built
 * for every cut that holds at every occupancy point the row allows, and for no
 * other. That has nothing to do with proofs, and is settled by enumerating
 * those points and looking, which the random corpus below does thousands of
 * times over. It is a stronger property than the search this replaced could
 * offer --- that one was allowed to refuse a valid cut, and did so about once
 * in twenty-five, which is a constraint the published inference procedure would
 * have posted and we could not justify.
 *
 * The second is that the emitted replay checks, which only veripb can say. Its
 * steps are individually sound whatever they are fed, so a mistake in the
 * bookkeeping --- a state linked to the wrong successor, a layer whose
 * at-least-one is not in fact complete --- shows up as a step that does not
 * follow rather than as a wrong answer. Every case here also pins its result,
 * and the "one better" cases pin something the derivation cannot support and
 * require a rejection: a right-hand side one smaller, and a coefficient one
 * larger.
 */

#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/innards/proofs/lifted_cover_cut.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>

#include <algorithm>
#include <cstddef>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <random>
#include <string>
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
        println(cerr, "lifted cover cut test failure: {}", message);
        std::exit(EXIT_FAILURE);
    }

    /// Does `sum pi_i a_i <= rhs` hold at every occupancy point the rows
    /// *jointly* allow? Brute force over all of them, which is the only oracle
    /// that does not beg the question. Several rows allow fewer points between
    /// them than any one of them does, which is exactly why a cut lifted over
    /// all of them can say more than one lifted over any single one.
    [[nodiscard]] auto valid(
        const vector<vector<Integer>> & demands, const vector<Integer> & capacities, const vector<Integer> & coefficients, Integer rhs) -> bool
    {
        for (unsigned long long mask = 0; mask < (1uLL << coefficients.size()); ++mask) {
            Integer weight = 0_i;
            vector<Integer> loads(capacities.size(), 0_i);
            for (size_t i = 0; i < coefficients.size(); ++i)
                if (mask & (1uLL << i)) {
                    for (size_t row = 0; row < capacities.size(); ++row)
                        loads[row] += demands[row][i];
                    weight += coefficients[i];
                }
            auto fits = true;
            for (size_t row = 0; row < capacities.size(); ++row)
                fits = fits && loads[row] <= capacities[row];
            if (fits && weight > rhs)
                return false;
        }
        return true;
    }

    /// The optimum the same enumeration reports, which is what a lifting
    /// subproblem asks for.
    [[nodiscard]] auto best(const vector<vector<Integer>> & demands, const vector<Integer> & capacities, const vector<Integer> & coefficients)
        -> Integer
    {
        auto most = 0_i;
        for (unsigned long long mask = 0; mask < (1uLL << coefficients.size()); ++mask) {
            Integer weight = 0_i;
            vector<Integer> loads(capacities.size(), 0_i);
            for (size_t i = 0; i < coefficients.size(); ++i)
                if (mask & (1uLL << i)) {
                    for (size_t row = 0; row < capacities.size(); ++row)
                        loads[row] += demands[row][i];
                    weight += coefficients[i];
                }
            auto fits = true;
            for (size_t row = 0; row < capacities.size(); ++row)
                fits = fits && loads[row] <= capacities[row];
            if (fits)
                most = std::max(most, weight);
        }
        return most;
    }

    /// A budget large enough that nothing here meets it. What happens when
    /// something does has its own case.
    const size_t generous = 100000;

    /// Validate the honest cut, emit its replay against a model with one row per
    /// capacity, pin `claimed_coefficients <= claimed_rhs`, and say whether
    /// veripb agreed. Each row carries one task the cut says nothing about, so
    /// the weakening sweep is exercised in every case rather than assumed.
    auto check(const string & name, const vector<vector<Integer>> & demands, const vector<Integer> & capacities, const vector<Integer> & coefficients,
        Integer rhs, const vector<Integer> & claimed_coefficients, Integer claimed_rhs, bool expect_veripb_to_accept, bool expect_valid = true)
        -> void
    {
        auto validity = validate_lifted_cover_cut(demands, coefficients, capacities, rhs, generous);
        if (validity.over_state_budget)
            fail(name + ": the programme went over a budget nothing here should reach");
        if (validity.cut.has_value() != expect_valid)
            fail(name + ": the dynamic programme " + (validity.cut ? "accepted" : "refused") + " the cut, expecting the opposite");
        if (validity.cut.has_value() != valid(demands, capacities, coefficients, rhs))
            fail(name + ": the dynamic programme disagrees with enumerating the rows' occupancy points");
        if (! validity.cut)
            return;

        auto proof_name = "lifted_cover_cut_" + name;
        ProofOptions proof_options{proof_name};
        NamesAndIDsTracker tracker(proof_options);
        ProofModel model(proof_options, tracker);

        vector<ProofFlag> flags;
        for (size_t i = 0; i < coefficients.size(); ++i)
            flags.push_back(model.create_proof_flag("task" + to_string(i)));

        // One extra task per row, with a term in it and no part in the cut, so
        // that every case has something to weaken out. The model gets every row,
        // including any the programme found could not bind; what is handed over
        // is only what it kept, which is what row_indices is for.
        vector<ProofLine> resources;
        vector<vector<ProofFlag>> weaken_out;
        for (size_t row = 0; row < capacities.size(); ++row) {
            WPBSum load;
            for (size_t i = 0; i < coefficients.size(); ++i)
                load += demands[row][i] * flags[i];
            auto spare = model.create_proof_flag("spare" + to_string(row));
            load += 1_i * spare;
            resources.push_back(model.add_labelled_constraint("resource" + to_string(row), move(load) <= capacities[row]));
            weaken_out.push_back({spare});
        }
        model.finalise();

        vector<ProofLine> kept_resources;
        vector<vector<ProofFlag>> kept_weaken_out;
        for (auto row : validity.cut->row_indices) {
            kept_resources.push_back(resources[row]);
            kept_weaken_out.push_back(weaken_out[row]);
        }

        ProofLogger logger(proof_options, tracker);
        tracker.switch_from_model_to_proof(&logger);
        logger.start_proof(model);
        tracker.emit_delayed_proof_steps();

        [[maybe_unused]] auto line = derive_lifted_cover_cut(
            logger, kept_resources, *validity.cut, flags, claimed_coefficients, kept_weaken_out, claimed_rhs, ProofLevel::Top);
        logger.conclude_none();
        tracker.finalise();

        auto accepted = run_veripb(proof_name + ".opb", proof_name + ".pbp");
        if (accepted != expect_veripb_to_accept)
            fail(name + ": veripb " + (accepted ? "accepted" : "rejected") + " it, expecting the opposite");
        dispose_of_proof_files(proof_name);
    }

    /// The single-row case, which is most of them and reads better without the
    /// extra braces.
    auto check(const string & name, const vector<Integer> & demands, Integer capacity, const vector<Integer> & coefficients, Integer rhs,
        const vector<Integer> & claimed_coefficients, Integer claimed_rhs, bool expect_veripb_to_accept, bool expect_valid = true) -> void
    {
        check(name, vector<vector<Integer>>{demands}, vector<Integer>{capacity}, coefficients, rhs, claimed_coefficients, claimed_rhs,
            expect_veripb_to_accept, expect_valid);
    }

    /// The honest cut, and then the two "one better" claims over it. Every
    /// certified artefact gets this treatment: with small integers a slack
    /// derivation can verify by coincidence, and a +1 rejection is what says the
    /// honest one is tight to its claim rather than merely true.
    auto check_and_claim_one_better(const string & name, const vector<vector<Integer>> & demands, const vector<Integer> & capacities,
        const vector<Integer> & coefficients, Integer rhs) -> void
    {
        check(name, demands, capacities, coefficients, rhs, coefficients, rhs, true);
        check(name + "_tighter_rhs", demands, capacities, coefficients, rhs, coefficients, rhs - 1_i, false);
        for (size_t i = 0; i < coefficients.size(); ++i) {
            auto raised = coefficients;
            raised[i] += 1_i;
            check(name + "_raised_" + to_string(i), demands, capacities, coefficients, rhs, raised, rhs, false);
        }
    }

    auto check_and_claim_one_better(
        const string & name, const vector<Integer> & demands, Integer capacity, const vector<Integer> & coefficients, Integer rhs) -> void
    {
        check_and_claim_one_better(name, vector<vector<Integer>>{demands}, vector<Integer>{capacity}, coefficients, rhs);
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    // The property that matters, and the one that needs no proof checker: the
    // dynamic programme is built exactly when the cut holds, and the optimum it
    // reports is the one enumeration reports. Most random claims here are
    // nonsense and have to be refused, and enough of the rest have to be real
    // for this to be saying something.
    {
        std::mt19937 rand(*get_seed());
        std::uniform_int_distribution<> n_dist(2, 5), rows_dist(1, 3), cap_dist(4, 15), coeff_dist(1, 3);
        size_t validated = 0, refused = 0, validated_non_unit = 0, validated_multi_row = 0, only_together = 0, largest_layer = 0;
        for (size_t trial = 0; trial < 4000; ++trial) {
            auto n = static_cast<size_t>(n_dist(rand));
            auto rows = static_cast<size_t>(rows_dist(rand));
            vector<Integer> capacities, coefficients;
            vector<vector<Integer>> demands(rows);
            for (size_t row = 0; row < rows; ++row) {
                capacities.push_back(Integer{cap_dist(rand)});
                std::uniform_int_distribution<> demand_dist(0, static_cast<int>(capacities[row].raw_value));
                for (size_t i = 0; i < n; ++i)
                    demands[row].push_back(Integer{demand_dist(rand)});
            }
            for (size_t i = 0; i < n; ++i)
                coefficients.push_back(Integer{coeff_dist(rand)});
            auto total = std::accumulate(coefficients.begin(), coefficients.end(), 0_i);
            std::uniform_int_distribution<> rhs_dist(0, static_cast<int>(total.raw_value));
            auto rhs = Integer{rhs_dist(rand)};

            auto validity = validate_lifted_cover_cut(demands, coefficients, capacities, rhs, generous);
            if (validity.over_state_budget)
                fail("the programme went over a budget these sizes cannot reach");
            if (validity.cut.has_value() != valid(demands, capacities, coefficients, rhs))
                fail("the dynamic programme disagrees with enumeration over " + to_string(n) + " members and " + to_string(rows) + " rows");

            // The same programme answering the question its inference half asks:
            // what is the most the left-hand side can be? Exactly, not an
            // over-estimate --- a lifting subproblem answered one too high is a
            // coefficient one too low, which is a different constraint from the
            // published procedure's.
            auto enumerated = best(demands, capacities, coefficients);
            auto optimum = lifted_cover_cut_optimum(demands, coefficients, capacities, total + 1_i, generous);
            if (optimum.over_state_budget || ! optimum.value)
                fail("the lifting subproblem gave no answer below a ceiling nothing can reach");
            if (*optimum.value != enumerated)
                fail("the lifting subproblem says " + to_string(optimum.value->raw_value) + " where enumeration says " +
                    to_string(enumerated.raw_value));

            // And that the ceiling really does cap rather than corrupt.
            auto capped = lifted_cover_cut_optimum(demands, coefficients, capacities, enumerated, generous);
            if (capped.value)
                fail("the lifting subproblem answered below a ceiling its answer reaches");

            if (! validity.cut) {
                ++refused;
                continue;
            }
            ++validated;
            if (*std::max_element(coefficients.begin(), coefficients.end()) > 1_i && total > rhs)
                ++validated_non_unit;
            if (validity.cut->row_indices.size() > 1) {
                ++validated_multi_row;
                // Does it need them all? A cut no single row implies is one the
                // single-resource certificate could not have reached at all.
                auto alone = false;
                for (size_t row = 0; row < rows && ! alone; ++row)
                    alone = valid({demands[row]}, {capacities[row]}, coefficients, rhs);
                if (! alone)
                    ++only_together;
            }
            for (const auto & layer : validity.cut->layers)
                largest_layer = std::max(largest_layer, layer.size());
        }
        println(cerr,
            "{} random cuts validated ({} with a non-unit coefficient and something to derive, {} needing more than one row, {} needing all of "
            "them), {} refused, the widest layer holding {} states",
            validated, validated_non_unit, validated_multi_row, only_together, refused, largest_layer);
        // A programme that refused everything would agree with enumeration on
        // the refusals alone and have derived nothing at all.
        if (validated < 100 || validated_non_unit < 10)
            fail("the random corpus is not exercising the dynamic programme: " + to_string(validated) + " validated, " +
                to_string(validated_non_unit) + " with a non-unit coefficient");
        // And one that never needed a second row would say nothing about the
        // thing this file was extended for.
        if (only_together < 10)
            fail("the random corpus found only " + to_string(only_together) + " cuts that need more than one row");
    }

    // Rows that cannot rule anything out are dropped rather than carried as a
    // flag per state saying nothing, and the caller's numbering survives it.
    {
        auto validity = validate_lifted_cover_cut({{1_i, 1_i}, {5_i, 5_i}}, {1_i, 1_i}, {10_i, 6_i}, 1_i, generous);
        if (! validity.cut)
            fail("the two-row cut with one useless row was refused");
        if (validity.cut->row_indices != vector<size_t>{1})
            fail("the row that cannot rule anything out was kept, or the wrong one was");
    }

    // A budget is a refusal that says so, rather than a cut quietly going
    // missing. Nothing else in this file is anywhere near it.
    {
        auto validity = validate_lifted_cover_cut(
            {{3_i, 3_i, 3_i, 3_i, 3_i, 3_i}, {1_i, 2_i, 3_i, 4_i, 5_i, 6_i}}, {1_i, 1_i, 1_i, 1_i, 1_i, 1_i}, {9_i, 12_i}, 3_i, 4);
        if (validity.cut || ! validity.over_state_budget)
            fail("a programme past its state budget was not refused as one");
    }
    println(cerr, "the programme decides validity and optima exactly, drops rows that cannot bind, and refuses to go over budget");

    if (! can_run_veripb()) {
        println(cerr, "veripb is not available, so the rest of this test is skipped");
        return EXIT_SUCCESS;
    }

    // Unit coefficients, which a single weaken-saturate-divide already reaches:
    // three sixes under ten is the clique, three fours under ten conflicts
    // nowhere and is a cardinality cut all the same.
    check_and_claim_one_better("clique", {6_i, 6_i, 6_i}, 10_i, {1_i, 1_i, 1_i}, 1_i);
    check_and_claim_one_better("cardinality", {4_i, 4_i, 4_i}, 10_i, {1_i, 1_i, 1_i}, 2_i);
    println(cerr, "unit coefficients derive, and a claim one better is rejected");

    // Lifting, where a cover of the small tasks is extended by the big one.
    // `a + b + c + d <= 2` from `5a + 3b + 3c + 3d <= 8` is not implied by the
    // row over the rationals, and its energy per unit of capacity beats the
    // row's: four over two against fourteen over eight.
    check_and_claim_one_better("lifted_unit", {5_i, 3_i, 3_i, 3_i}, 8_i, {1_i, 1_i, 1_i, 1_i}, 2_i);
    println(cerr, "a lifted cover cut derives");

    // Non-unit coefficients, which are what this file exists for and what no
    // single weaken/saturate/divide can reach.
    check_and_claim_one_better("non_unit", {5_i, 2_i, 2_i, 2_i}, 5_i, {2_i, 1_i, 1_i, 1_i}, 2_i);
    check_and_claim_one_better("non_unit_wider", {7_i, 3_i, 3_i, 3_i, 3_i}, 9_i, {2_i, 1_i, 1_i, 1_i, 1_i}, 3_i);
    println(cerr, "non-unit coefficients derive");

    // What the search this replaced could not reach at all. `3a + 2b + 2c + 2d
    // <= 4` holds at every point `6a + 3b + 3c + 3d <= 8` allows, and no
    // sequence of weakenings, saturations and divisions of that row arrives at
    // it; a replay of the programme has nothing to arrive at, so it derives.
    check_and_claim_one_better("beyond_the_old_search", {6_i, 3_i, 3_i, 3_i}, 8_i, {3_i, 2_i, 2_i, 2_i}, 4_i);
    println(cerr, "a cut no short cutting-planes route reaches derives too");

    // A cut where the `pol` that rules a member out is the only thing that does.
    // Elsewhere the checker reaches the same conclusion unaided: a state's weight
    // bound usually pins the members it counts, or the residual capacity left
    // after taking the next one does, and either way unit propagation gets there
    // without being told. Neither happens here --- two of four unit-demand
    // members reach a weight of two and nothing says which, and taking the
    // demand-four member still leaves room for one of them --- so removing that
    // step makes veripb reject this case, and it rejects no other.
    check_and_claim_one_better("row_not_pinned", {1_i, 1_i, 1_i, 1_i, 4_i}, 5_i, {1_i, 1_i, 1_i, 1_i, 3_i}, 4_i);
    println(cerr, "a cut whose states leave the row slack derives, which needs the row step");

    // The restrictions a derived constraint meets at the edges of its window,
    // where only some of its tasks have flags. The coefficients cannot move ---
    // a Cumulative has one height per task --- so the cut is simply restricted,
    // and the degenerate end of that is a cut no 0/1 point can miss, which is
    // one RUP and no dynamic programme at all.
    check("restricted", {5_i, 3_i, 3_i}, 8_i, {1_i, 1_i, 1_i}, 2_i, {1_i, 1_i, 1_i}, 2_i, true);
    check("restricted_trivial", {5_i, 3_i}, 8_i, {1_i, 1_i}, 2_i, {1_i, 1_i}, 2_i, true);
    println(cerr, "a cut restricted to fewer tasks still derives, or is trivial");

    // A cut that is not valid has no programme to build and no proof to emit.
    check("invalid_rhs", {6_i, 6_i, 6_i}, 10_i, {1_i, 1_i, 1_i}, 0_i, {1_i, 1_i, 1_i}, 0_i, false, false);
    println(cerr, "an invalid cut is refused rather than derived");

    // Several rows, which is what Sidorov's Equation 4 lifts over and where a
    // certificate built around a single one stops. Two resources of capacity
    // five, each with one task that fills it and three that half do: `2a + b + c
    // + 2d <= 2` holds at every point the two allow between them, and at neither
    // resource's own points --- the first admits {b, d} for three, and the second
    // {a, b} for three. So this is not the single-row cut with extra rows
    // watching: it is a constraint no single row implies, and the only thing
    // that changed is that the programme carries a weight per row.
    check_and_claim_one_better("two_rows", {{5_i, 2_i, 2_i, 2_i}, {2_i, 2_i, 2_i, 5_i}}, {5_i, 5_i}, {2_i, 1_i, 1_i, 2_i}, 2_i);
    check("two_rows_one_alone", {5_i, 2_i, 2_i, 2_i}, 5_i, {2_i, 1_i, 1_i, 2_i}, 2_i, {2_i, 1_i, 1_i, 2_i}, 2_i, false, false);
    check("two_rows_other_alone", {2_i, 2_i, 2_i, 5_i}, 5_i, {2_i, 1_i, 1_i, 2_i}, 2_i, {2_i, 1_i, 1_i, 2_i}, 2_i, false, false);
    println(cerr, "a cut needing two rows derives, and neither row derives it alone");

    // Three of them, each ruling out one pair, which is the shape a cut lifted
    // across a project's resources actually has: no resource is where the
    // argument lives, and every one of them is doing some of it.
    check_and_claim_one_better("three_rows", {{3_i, 3_i, 1_i}, {1_i, 3_i, 3_i}, {3_i, 1_i, 3_i}}, {5_i, 5_i, 5_i}, {1_i, 1_i, 1_i}, 1_i);
    println(cerr, "a cut whose rows each rule out one pair derives");

    // A row that cannot rule anything out is not in the programme, so a cut
    // beside one derives exactly as it does without it --- and the caller's
    // numbering of its rows is what it passes, not the programme's.
    check_and_claim_one_better("useless_row_beside", {{1_i, 1_i, 1_i}, {6_i, 6_i, 6_i}}, {20_i, 10_i}, {1_i, 1_i, 1_i}, 1_i);
    println(cerr, "a row that cannot bind is dropped without disturbing the rest");

    return EXIT_SUCCESS;
}
