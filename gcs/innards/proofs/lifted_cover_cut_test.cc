/* Deriving a lifted cover cut from a capacity row.
 *
 * Nothing here goes near a Cumulative: the routine's whole job is the cutting-
 * planes arithmetic, so it is tested on a micro model whose only constraint is
 * one resource row --- and that model is *satisfiable* (everything false fits
 * under any non-negative capacity), which matters, since against an
 * unsatisfiable one every step is vacuously valid and a corrupted derivation
 * would sail through.
 *
 * Two things are being checked, and they are checked by different means.
 *
 * The first is that a plan is never made for a cut that is not valid. That has
 * nothing to do with proofs: it is settled by enumerating every occupancy point
 * the row allows and looking, which the random corpus below does thousands of
 * times over. A lifted inequality's validity is coNP-hard to decide in general,
 * so this is the property that matters --- the planner is allowed to refuse a
 * valid cut it cannot derive, and is not allowed to plan an invalid one.
 *
 * The second is that the emitted `pol`s land where the plan predicted, which
 * only veripb can say. The prediction is a model of VeriPB's normalised-form
 * arithmetic, and a model that has drifted from the real thing would produce
 * plans that derive *something* --- every step is sound whatever it is fed ---
 * just not the line claimed. The `ia` pin is what turns that into a rejection,
 * since its implication check is syntactic. So every case here pins, and the
 * "one better" cases pin something the derivation cannot support and require a
 * rejection: a right-hand side one smaller, and a coefficient one larger.
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
    const size_t max_covers = 4096;

    auto fail(const string & message) -> void
    {
        println(cerr, "lifted cover cut test failure: {}", message);
        std::exit(EXIT_FAILURE);
    }

    /// Does `sum pi_i a_i <= rhs` hold at every occupancy point the row allows?
    /// Brute force over all of them, which is the only oracle that does not
    /// beg the question.
    [[nodiscard]] auto valid(const vector<Integer> & demands, Integer capacity, const vector<Integer> & coefficients, Integer rhs) -> bool
    {
        for (unsigned long long mask = 0; mask < (1uLL << demands.size()); ++mask) {
            Integer load = 0_i, weight = 0_i;
            for (size_t i = 0; i < demands.size(); ++i)
                if (mask & (1uLL << i)) {
                    load += demands[i];
                    weight += coefficients[i];
                }
            if (load <= capacity && weight > rhs)
                return false;
        }
        return true;
    }

    /// Plan the honest cut, emit it against a one-row model, pin
    /// `claimed_coefficients <= claimed_rhs`, and say whether veripb agreed.
    /// The model carries one task the cut says nothing about, so the weakening
    /// sweep is exercised in every case rather than assumed.
    auto check(const string & name, const vector<Integer> & demands, Integer capacity, const vector<Integer> & coefficients, Integer rhs,
        const vector<Integer> & claimed_coefficients, Integer claimed_rhs, bool expect_veripb_to_accept, bool expect_plan = true) -> void
    {
        auto plan = plan_lifted_cover_cut(demands, coefficients, capacity, rhs, max_covers);
        if (plan.has_value() != expect_plan)
            fail(name + ": the planner " + (plan ? "found" : "refused") + " a derivation, expecting the opposite");
        if (! plan)
            return;

        if (! valid(demands, capacity, coefficients, rhs))
            fail(name + ": a plan was made for a cut that is not valid");

        auto proof_name = "lifted_cover_cut_" + name;
        ProofOptions proof_options{proof_name};
        NamesAndIDsTracker tracker(proof_options);
        ProofModel model(proof_options, tracker);

        // One extra task with a term in the row and no part in the cut, so
        // that every case has something to weaken out.
        vector<ProofFlag> flags;
        WPBSum load;
        for (size_t i = 0; i < demands.size(); ++i) {
            flags.push_back(model.create_proof_flag("task" + to_string(i)));
            load += demands[i] * flags[i];
        }
        auto spare = model.create_proof_flag("spare");
        load += 1_i * spare;
        auto resource = model.add_labelled_constraint("resource", move(load) <= capacity);
        model.finalise();

        ProofLogger logger(proof_options, tracker);
        tracker.switch_from_model_to_proof(&logger);
        logger.start_proof(model);
        tracker.emit_delayed_proof_steps();

        [[maybe_unused]] auto line =
            derive_lifted_cover_cut(logger, resource, *plan, flags, claimed_coefficients, {spare}, claimed_rhs, ProofLevel::Top);
        logger.conclude_none();
        tracker.finalise();

        auto accepted = run_veripb(proof_name + ".opb", proof_name + ".pbp");
        if (accepted != expect_veripb_to_accept)
            fail(name + ": veripb " + (accepted ? "accepted" : "rejected") + " it, expecting the opposite");
        dispose_of_proof_files(proof_name);
    }

    /// The honest cut, and then the two "one better" claims over it. Every
    /// certified artefact gets this treatment: with small integers a slack
    /// derivation can verify by coincidence, and a +1 rejection is what says
    /// the honest one is tight to its claim rather than merely true.
    auto check_and_claim_one_better(
        const string & name, const vector<Integer> & demands, Integer capacity, const vector<Integer> & coefficients, Integer rhs) -> void
    {
        check(name, demands, capacity, coefficients, rhs, coefficients, rhs, true);
        check(name + "_tighter_rhs", demands, capacity, coefficients, rhs, coefficients, rhs - 1_i, false);
        for (size_t i = 0; i < coefficients.size(); ++i) {
            auto raised = coefficients;
            raised[i] += 1_i;
            check(name + "_raised_" + to_string(i), demands, capacity, coefficients, rhs, raised, rhs, false);
        }
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    // The property that matters, and the one that needs no proof checker: a
    // plan is never made for a cut that is not valid. Most random claims here
    // are nonsense, and the planner has to refuse all of them while still
    // finding enough real ones for this to be saying something.
    {
        std::mt19937 rand(*get_seed());
        std::uniform_int_distribution<> n_dist(2, 5), cap_dist(4, 15), coeff_dist(1, 3);
        size_t planned = 0, refused = 0, planned_non_unit = 0;
        for (size_t trial = 0; trial < 4000; ++trial) {
            auto n = static_cast<size_t>(n_dist(rand));
            auto capacity = Integer{cap_dist(rand)};
            vector<Integer> demands, coefficients;
            std::uniform_int_distribution<> demand_dist(1, static_cast<int>(capacity.raw_value));
            for (size_t i = 0; i < n; ++i) {
                demands.push_back(Integer{demand_dist(rand)});
                coefficients.push_back(Integer{coeff_dist(rand)});
            }
            auto total = std::accumulate(coefficients.begin(), coefficients.end(), 0_i);
            std::uniform_int_distribution<> rhs_dist(0, static_cast<int>(total.raw_value));
            auto rhs = Integer{rhs_dist(rand)};

            auto plan = plan_lifted_cover_cut(demands, coefficients, capacity, rhs, max_covers);
            if (! plan) {
                ++refused;
                continue;
            }
            if (! valid(demands, capacity, coefficients, rhs))
                fail("planned an invalid cut over demands " + to_string(demands.size()) + " and capacity " + to_string(capacity.raw_value));
            ++planned;
            if (*std::max_element(coefficients.begin(), coefficients.end()) > 1_i && ! plan->empty())
                ++planned_non_unit;
        }
        println(
            cerr, "{} random cuts planned ({} with a non-unit coefficient), {} refused, none of them invalid", planned, planned_non_unit, refused);
        // A planner that refused everything would pass the line above without
        // having derived anything at all.
        if (planned < 100 || planned_non_unit < 10)
            fail("the random corpus is not exercising the planner: " + to_string(planned) + " plans, " + to_string(planned_non_unit) +
                " with a non-unit coefficient");
    }

    if (! can_run_veripb()) {
        println(cerr, "veripb is not available, so the rest of this test is skipped");
        return EXIT_SUCCESS;
    }

    // Unit coefficients: what build_am1_from_row already recovers, reached here
    // through the free divisor instead of the fixed one. Three sixes under ten
    // is the clique; three fours under ten conflicts nowhere and is a
    // cardinality cut all the same.
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
    // single weaken/saturate/divide can reach: one copy of the row plus one of
    // the cover cut, over three.
    check_and_claim_one_better("non_unit", {5_i, 2_i, 2_i, 2_i}, 5_i, {2_i, 1_i, 1_i, 1_i}, 2_i);
    check_and_claim_one_better("non_unit_wider", {7_i, 3_i, 3_i, 3_i, 3_i}, 9_i, {2_i, 1_i, 1_i, 1_i, 1_i}, 3_i);
    println(cerr, "non-unit coefficients derive, through a cover and a lifting step");

    // The restrictions a derived constraint meets at the edges of its window,
    // where only some of its tasks have flags. The coefficients cannot move ---
    // a Cumulative has one height per task --- so only the route may, and the
    // degenerate end of that is a cut no 0/1 point can miss, which is one RUP
    // and no arithmetic.
    check("restricted", {5_i, 3_i, 3_i}, 8_i, {1_i, 1_i, 1_i}, 2_i, {1_i, 1_i, 1_i}, 2_i, true);
    check("restricted_trivial", {5_i, 3_i}, 8_i, {1_i, 1_i}, 2_i, {1_i, 1_i}, 2_i, true);
    println(cerr, "a cut restricted to fewer tasks still derives, or is trivial");

    // Refusals. A cut that is not valid has no derivation to find, and one that
    // is valid but out of reach is refused rather than asserted: `3a + 2b + 2c
    // + 2d <= 4` holds at every point the row allows, and nothing in the shapes
    // this routine knows arrives at it.
    check("invalid_rhs", {6_i, 6_i, 6_i}, 10_i, {1_i, 1_i, 1_i}, 0_i, {1_i, 1_i, 1_i}, 0_i, false, false);
    println(cerr, "an invalid cut is refused rather than derived");

    return EXIT_SUCCESS;
}
