#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/subset_sum_strengthening.hh>

#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <optional>
#include <random>
#include <string>
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
using std::string;
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
        println(cerr, "subset sum strengthening test failure: {}", message);
        std::exit(EXIT_FAILURE);
    }

    // The answer, from the definition: every subset, summed.
    auto brute_force_largest(const vector<Integer> & weights, Integer bound) -> Integer
    {
        Integer best = 0_i;
        for (unsigned long long subset = 0; subset < (1ull << weights.size()); ++subset) {
            Integer sum = 0_i;
            for (size_t i = 0; i < weights.size(); ++i)
                if (subset & (1ull << i))
                    sum += weights[i];
            if (sum <= bound && sum > best)
                best = sum;
        }
        return best;
    }

    auto check_algorithm(const vector<Integer> & weights, Integer bound) -> void
    {
        auto computed = largest_subset_sum_at_most(weights, bound);
        auto expected = brute_force_largest(weights, bound);
        if (computed != expected) {
            println(cerr, "largest_subset_sum_at_most({}, {}) = {}, brute force says {}", weights, bound.raw_value, computed.raw_value,
                expected.raw_value);
            fail("algorithmic property");
        }
    }

    struct Fixture
    {
        string name;
        vector<Integer> weights;
        Integer bound;
        Integer expected;
        bool expect_division;
    };

    // Which micro model a proof is checked against. The distinction matters:
    // an OPB that is itself unsatisfiable makes *every* RUP step valid, so a
    // corrupted derivation sails through one.
    enum class Model
    {
        // Just the source line, so the model is satisfiable and every step of
        // the derivation has to stand on its own.
        SourceOnly,
        // The source line plus an axiom putting the sum above the strengthened
        // bound. Nothing satisfies both --- no subset sums into the gap ---
        // but as inequalities over the rationals the two are consistent, so
        // combining them into a contradiction takes the strengthening. This is
        // the end-to-end demonstration that the line is usable.
        WithContradiction
    };

    // Two things are checked about the derivation, and they are different
    // things. veripb accepting every step says each one followed; it does not
    // say the line that came back is the one the caller was promised, because
    // a sound step can land somewhere weaker. So each proof also pins the
    // line's content with an `ia` step, whose implication check is syntactic:
    // a weaker line does not imply the claimed one and veripb says so.
    auto check_proof(const Fixture & fixture, SubsetSumMutation mutation, Model model_kind, const string & tag, bool expect_veripb_to_accept) -> void
    {
        auto proof_name = "subset_sum_strengthening_" + fixture.name + "_" + tag;
        ProofOptions proof_options{proof_name};
        NamesAndIDsTracker tracker(proof_options);
        ProofModel model(proof_options, tracker);

        vector<SubsetSumItem> items;
        WPBSum sum;
        for (size_t i = 0; i < fixture.weights.size(); ++i) {
            auto flag = model.create_proof_flag("item" + std::to_string(i));
            items.push_back(SubsetSumItem{fixture.weights[i], flag});
            sum += fixture.weights[i] * flag;
        }

        // Labelled, because a pol step may only reference an OPB row by name:
        // a re-derived model has a different row count.
        auto source = model.add_labelled_constraint("source", WPBSum{sum} <= fixture.bound);
        std::optional<ProofLine> too_big;
        if (model_kind == Model::WithContradiction)
            too_big = model.add_labelled_constraint("toobig", WPBSum{sum} >= fixture.expected + 1_i);
        model.finalise();

        ProofLogger logger(proof_options, tracker);
        tracker.switch_from_model_to_proof(&logger);
        logger.start_proof(model);
        tracker.emit_delayed_proof_steps();

        auto strengthening = derive_subset_sum_strengthening(logger, items, source, fixture.bound, ProofLevel::Top, mutation);

        if (std::holds_alternative<subset_sum_mutation::None>(mutation)) {
            if (strengthening.bound != fixture.expected)
                fail(fixture.name + ": strengthened to " + std::to_string(strengthening.bound.raw_value) + ", expected " +
                    std::to_string(fixture.expected.raw_value));
            if (strengthening.by_division != fixture.expect_division)
                fail(fixture.name + ": took the " + (strengthening.by_division ? "divisibility" : "dynamic programming") +
                    " path, expected the other");
        }

        // The line must carry the bound the utility is supposed to establish,
        // which is the fixture's, whatever a mutated run reported back.
        logger.emit(ImpliesProofRule{strengthening.line}, WPBSum{sum} <= fixture.expected, ProofLevel::Top);

        if (too_big) {
            PolBuilder contradiction;
            contradiction.add(strengthening.line).add(*too_big);
            auto combined = contradiction.emit(logger, ProofLevel::Top);
            // And that combination must really be a contradiction, rather than
            // something the checker can refute by other means: `ia` against the
            // pol's own line is what says so.
            logger.emit(ImpliesProofRule{combined}, WPBSum{} >= 1_i, ProofLevel::Top);
            logger.conclude_unsatisfiable(false);
        }
        else
            logger.conclude_none();

        tracker.finalise();

        auto accepted = run_veripb(proof_name + ".opb", proof_name + ".pbp");
        if (accepted != expect_veripb_to_accept) {
            if (accepted)
                fail(fixture.name + " (" + tag +
                    "): veripb accepted a proof built from a deliberately corrupted derivation, so the honest one has slack in it");
            else
                fail(fixture.name + " (" + tag + "): veripb rejected an honest proof");
        }
        dispose_of_proof_files(proof_name);
    }
}

auto main(int argc, char * argv[]) -> int
{
    // Sharpness fixtures, verified by hand in the comments: each is chosen so
    // that arithmetic which is only right by coincidence gets it wrong.
    const vector<Fixture> fixtures{// Pairwise gcds all exceed one, but the overall gcd is one, so the
        // divisibility path must not fire: 6 + 10 = 16 > 14, so the reachable
        // sums under 14 are 0, 6, 10.
        {"a", {6_i, 10_i, 15_i}, 14_i, 10_i, false},
        // The same weights, with room for two of them: 6 + 10 = 16,
        // 6 + 15 = 21, 10 + 15 = 25, and 6 + 10 + 15 = 31 is over. A gap of
        // five below the bound.
        {"b", {6_i, 10_i, 15_i}, 30_i, 25_i, false},
        // Large coprime weights, one item's worth of room: 31 + 37 = 68 is
        // over, so the answer is the largest single weight.
        {"c", {31_i, 37_i, 41_i}, 67_i, 41_i, false},
        // The same weights with four more units of room, which is enough for
        // exactly one pair: 31 + 37 = 68, and 31 + 41 = 72 is over.
        {"d", {31_i, 37_i, 41_i}, 71_i, 68_i, false},
        // Every weight even, an odd bound: divisibility rounds it down by one,
        // and that happens to be reachable (6 + 15 does not arise here).
        {"e", {6_i, 10_i, 14_i}, 17_i, 16_i, true},
        // Every weight a multiple of six, a bound between two multiples.
        {"f", {6_i, 12_i, 18_i}, 29_i, 24_i, true},
        // A single item, out of reach. One weight is its own gcd, so this is
        // the divisibility path with a quotient of zero.
        {"g", {7_i}, 5_i, 0_i, true},
        // A single item, within reach but with room to spare.
        {"h", {7_i}, 9_i, 7_i, true},
        // A bound above everything: the answer is the whole sum.
        {"i", {3_i, 5_i, 11_i}, 40_i, 19_i, false},
        // A bound of zero: nothing fits.
        {"j", {3_i, 5_i}, 0_i, 0_i, false},
        // At the scale the consumers work at: six coprime weights against a
        // bound in the eighties, which is sixteen reachable states across
        // seven layers. Not a stress test --- a check that the layered
        // derivation stays a sensible size when the bound is realistic, since
        // it is O(items x bound) flags in the worst case.
        {"k", {29_i, 31_i, 37_i, 41_i, 43_i, 47_i}, 83_i, 80_i, false}};

    for (const auto & fixture : fixtures) {
        auto expected = brute_force_largest(fixture.weights, fixture.bound);
        if (expected != fixture.expected)
            fail(fixture.name + ": the fixture's own expected value is wrong; brute force says " + std::to_string(expected.raw_value));
        check_algorithm(fixture.weights, fixture.bound);
    }

    // The contract's degenerate cases, where the answer is the bound itself
    // and there is nothing to derive.
    if (largest_subset_sum_at_most({6_i, 10_i, 15_i}, 16_i) != 16_i)
        fail("a reachable bound must come back unchanged");
    if (largest_subset_sum_at_most({}, 12_i) != 0_i)
        fail("an empty item list must give zero");
    if (largest_subset_sum_at_most({3_i, 5_i, 11_i}, 19_i) != 19_i)
        fail("a bound equal to the total must come back unchanged");

    // Random weight sets against brute force. Mixtures of primes,
    // near-duplicates and gcd-structured sets, since each hides a different
    // kind of arithmetic slip.
    {
        auto seed = 1u;
        for (int a = 1; a < argc; ++a)
            if (string{argv[a]}.starts_with("--seed="))
                seed = static_cast<unsigned>(std::stoul(string{argv[a]}.substr(7)));
        println(cerr, "subset_sum_strengthening_test: random seed is {} (reproduce with --seed={})", seed, seed);

        std::mt19937 rand(seed);
        std::uniform_int_distribution<> n_dist(0, 12), weight_dist(1, 200), bound_dist(0, 400), family_dist(0, 2);
        for (int k = 0; k < 400; ++k) {
            vector<Integer> weights;
            auto n = n_dist(rand);
            auto family = family_dist(rand);
            auto base = weight_dist(rand);
            for (int i = 0; i < n; ++i)
                switch (family) {
                case 0: weights.push_back(Integer{weight_dist(rand)}); break;                                  // anything
                case 1: weights.push_back(Integer{base + std::uniform_int_distribution<>(0, 2)(rand)}); break; // near-duplicates
                default: weights.push_back(Integer{6 * std::uniform_int_distribution<>(1, 30)(rand)}); break;  // gcd-structured
                }
            check_algorithm(weights, Integer{bound_dist(rand)});
        }
    }

    if (! can_run_veripb()) {
        println(cerr, "veripb is not available, so the proof-level checks are skipped");
        return EXIT_SUCCESS;
    }

    for (const auto & fixture : fixtures) {
        // A fixture whose bound is already reachable has nothing to derive, so
        // there is no proof to check; every fixture here is chosen otherwise.
        println(cerr, "subset sum strengthening {}: weights {} bound {} to {}", fixture.name, fixture.weights, fixture.bound.raw_value,
            fixture.expected.raw_value);
        check_proof(fixture, subset_sum_mutation::None{}, Model::SourceOnly, "honest", true);
        check_proof(fixture, subset_sum_mutation::None{}, Model::WithContradiction, "usable", true);
    }

    // Mutations. Each must be rejected: if one is not, the honest derivation
    // was not doing the work it looks like it is doing.
    for (const auto & fixture : fixtures) {
        if (fixture.expected == 0_i)
            continue; // nothing to claim one better than
        println(cerr, "subset sum strengthening {}: mutations", fixture.name);
        // Claiming one better makes a step of the derivation unsupported, so
        // it is the satisfiable model that sees it.
        check_proof(fixture, subset_sum_mutation::ClaimOneBetter{}, Model::SourceOnly, "onebetter", false);
        // A divisor that does not divide everything still divides soundly ---
        // the step verifies. What it does not do is establish the claimed
        // bound, and that only shows up where the line gets used.
        check_proof(fixture, subset_sum_mutation::BogusDivisor{}, Model::WithContradiction, "bogusdivisor", false);
        if (! fixture.expect_division && fixture.weights.size() > 2)
            check_proof(fixture, subset_sum_mutation::SkipALayer{}, Model::SourceOnly, "skiplayer", false);
    }

    return EXIT_SUCCESS;
}
