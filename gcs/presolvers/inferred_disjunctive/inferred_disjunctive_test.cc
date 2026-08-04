/* Inferring Disjunctive constraints from cliques in the cross-resource conflict
 * graph.
 *
 * The fixture family is the one the issue asks for, and it is built so that no
 * single posted Cumulative can make the inference: k tasks and k resources,
 * with the pair (i, j) conflicting only on resource (i + j) mod k. Every
 * resource sees exactly one conflicting pair, so the clique exists only in the
 * union of them --- which is what makes a root refutation here evidence of
 * something, rather than evidence that one of the donors was enough.
 *
 * The sharp twin is the same instance with one more unit of horizon, where the
 * tasks fit exactly. That has to stay satisfiable with the presolver on, and to
 * report the same solutions as brute force, since an inferred constraint that
 * quietly removed one would otherwise look like a success.
 */

#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/presolvers/inferred_disjunctive/inferred_disjunctive.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <set>
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
using std::ifstream;
using std::make_optional;
using std::make_shared;
using std::move;
using std::nullopt;
using std::optional;
using std::set;
using std::shared_ptr;
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
        println(cerr, "inferred disjunctive test failure: {}", message);
        std::exit(EXIT_FAILURE);
    }

    struct Setup
    {
        bool presolve = true;
        CumulativeRules rules = CumulativeRules{};
        optional<CumulativeRules> inferred_rules = nullopt;
        std::size_t min_clique_size = 3;
        std::size_t max_candidates = 100, max_posted = 5;
        shared_ptr<InferredDisjunctiveStats> stats = nullptr;
    };

    /* k tasks of length p, and k resources of capacity one. Resource r carries
     * demand one for exactly the two tasks i, j with (i + j) mod k == r, and
     * zero for everyone else --- so it forbids that one pair overlapping and
     * says nothing about any other.
     *
     * Every resource is posted over all k starts, so a task keeps the same
     * position everywhere, and the zero demands drop it out of that resource's
     * flags exactly as a real model's would.
     */
    auto post_family(Problem & p, int k, int length, int horizon, const Setup & setup) -> vector<IntegerVariableID>
    {
        vector<IntegerVariableID> starts;
        for (int i = 0; i < k; ++i)
            starts.push_back(p.create_integer_variable(0_i, Integer{horizon - length}, "s" + to_string(i)));

        vector<Integer> lengths(static_cast<size_t>(k), Integer{length});
        for (int r = 0; r < k; ++r) {
            vector<Integer> heights(static_cast<size_t>(k), 0_i);
            for (int i = 0; i < k; ++i)
                for (int j = i + 1; j < k; ++j)
                    if ((i + j) % k == r) {
                        heights[static_cast<size_t>(i)] = 1_i;
                        heights[static_cast<size_t>(j)] = 1_i;
                    }
            p.post(Cumulative{starts, lengths, heights, 1_i}.with_rules(setup.rules));
        }

        if (setup.presolve) {
            auto presolver = InferredDisjunctive{setup.stats};
            presolver.with_budgets(setup.max_candidates, setup.max_posted).with_minimum_clique_size(setup.min_clique_size);
            if (setup.inferred_rules)
                presolver.with_rules(*setup.inferred_rules);
            p.add_presolver(presolver);
        }
        return starts;
    }

    struct Outcome
    {
        set<vector<int>> solutions;
        unsigned long long recursions = 0;
        bool refuted_at_root = false;
    };

    auto solve_family(int k, int length, int horizon, const Setup & setup, const optional<string> & proof_name, bool verify = true) -> Outcome
    {
        Problem p;
        auto starts = post_family(p, k, length, horizon, setup);

        Outcome outcome;
        bool reached_a_node = false, found_a_solution = false;
        auto stats = solve_with(p,
            SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
                               found_a_solution = true;
                               vector<int> solution;
                               for (const auto & v : starts)
                                   solution.push_back(s(v).raw_value);
                               outcome.solutions.insert(move(solution));
                               return true;
                           },
                .trace = [&](const CurrentState &) -> bool {
                    reached_a_node = true;
                    return true;
                }},
            proof_name ? make_optional<ProofOptions>(ProofFileNames{*proof_name}) : nullopt);

        outcome.recursions = stats.recursions;
        outcome.refuted_at_root = ! reached_a_node && ! found_a_solution;

        if (proof_name && verify)
            verify_proof_and_clean_up(*proof_name);
        return outcome;
    }

    /// Brute force over the same family: every start assignment where no two
    /// tasks sharing a resource overlap.
    auto expected_solutions(int k, int length, int horizon) -> set<vector<int>>
    {
        set<vector<int>> expected;
        vector<int> current(static_cast<size_t>(k), 0);
        auto ok = [&]() {
            for (int i = 0; i < k; ++i)
                for (int j = i + 1; j < k; ++j)
                    if (current[static_cast<size_t>(i)] < current[static_cast<size_t>(j)] + length &&
                        current[static_cast<size_t>(j)] < current[static_cast<size_t>(i)] + length)
                        return false;
            return true;
        };
        auto recurse = [&](auto && self, int at) -> void {
            if (at == k) {
                if (ok())
                    expected.insert(current);
                return;
            }
            for (int s = 0; s <= horizon - length; ++s) {
                current[static_cast<size_t>(at)] = s;
                self(self, at + 1);
            }
        };
        recurse(recurse, 0);
        return expected;
    }

    auto read_file(const string & name) -> string
    {
        ifstream in{name, std::ios::binary};
        if (! in)
            fail("could not read " + name);
        return string{std::istreambuf_iterator<char>{in}, std::istreambuf_iterator<char>{}};
    }

    auto count_occurrences(const string & haystack, const string & needle) -> size_t
    {
        size_t count = 0;
        for (auto at = haystack.find(needle); at != string::npos; at = haystack.find(needle, at + needle.size()))
            ++count;
        return count;
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);
    auto proofs = can_run_veripb();

    // Three tasks of length two, pairwise incompatible, into five time points.
    // Six units of work and five slots, so it cannot be done --- but only the
    // clique says so, since each resource on its own sees one pair.
    {
        auto stats = make_shared<InferredDisjunctiveStats>();

        auto donors_only = solve_family(3, 2, 5, Setup{.presolve = false}, nullopt);
        if (donors_only.refuted_at_root)
            fail("the donors alone refuted at the root, so the fixture proves nothing");

        auto inferred = solve_family(3, 2, 5, Setup{.stats = stats}, proofs ? make_optional("inferred_disjunctive_unsat") : nullopt);

        if (stats->cliques_posted != 1)
            fail("posted " + to_string(stats->cliques_posted) + " cliques, not the one the family contains");
        if (stats->clique_members_posted != 3)
            fail("the posted clique had " + to_string(stats->clique_members_posted) + " members, not three");
        if (stats->cross_donor_pairs == 0)
            fail("no pair needed bridging, so the fixture is not exercising the cross-resource case");
        if (proofs && stats->bridges_derived == 0)
            fail("no flag bridge was derived, so the certificate is not spanning resources");
        if (! inferred.refuted_at_root)
            fail("the inferred constraint did not refute at the root");
        if (! inferred.solutions.empty())
            fail("the instance is unsatisfiable but solutions were reported");

        println(cerr, "cross-resource clique: refuted at the root against {} nodes without it, {} bridges", donors_only.recursions,
            stats->bridges_derived);
    }

    // The sharp twin: one more unit of horizon and the three tasks fit exactly.
    // Still satisfiable, still every solution, and the clique is still posted
    // --- an inferred constraint has to be harmless where it is not decisive.
    {
        auto stats = make_shared<InferredDisjunctiveStats>();
        auto inferred = solve_family(3, 2, 6, Setup{.stats = stats}, proofs ? make_optional("inferred_disjunctive_sat") : nullopt);

        if (stats->cliques_posted != 1)
            fail("sharp twin: the clique was not posted, so the comparison is vacuous");
        auto expected = expected_solutions(3, 2, 6);
        if (expected.empty())
            fail("sharp twin: the fixture has no solutions, so it is not the twin it claims to be");
        if (inferred.solutions != expected)
            fail("sharp twin: solutions do not match brute force, so the inferred constraint removed some");
        println(cerr, "sharp twin: {} solutions, matching brute force", inferred.solutions.size());
    }

    // Solution preservation over the family, at several shapes.
    for (auto [k, length, horizon] : {std::tuple{3, 2, 7}, std::tuple{3, 1, 4}, std::tuple{4, 1, 5}}) {
        auto stats = make_shared<InferredDisjunctiveStats>();
        auto inferred = solve_family(k, length, horizon, Setup{.stats = stats}, nullopt);
        auto expected = expected_solutions(k, length, horizon);
        if (inferred.solutions != expected)
            fail("k=" + to_string(k) + " length=" + to_string(length) + " horizon=" + to_string(horizon) + ": solutions do not match brute force");
    }
    println(cerr, "solution preservation: three shapes match brute force");

    // The inference is time-table neutral, for the same reason
    // CumulativeStrengthening's is: a conflicting pair is already kept apart by
    // whichever resource witnesses it, so the inferred constraint's profile
    // reasoning cannot say anything new. With the energy rules off everywhere,
    // the node counts must be identical.
    {
        const CumulativeRules tt_only{.time_table = true, .overload = false, .profile_overload = false};
        auto stats = make_shared<InferredDisjunctiveStats>();

        auto without = solve_family(3, 2, 6, Setup{.presolve = false, .rules = tt_only}, nullopt);
        auto with = solve_family(3, 2, 6, Setup{.rules = tt_only, .inferred_rules = make_optional(tt_only), .stats = stats}, nullopt);

        if (stats->cliques_posted != 1)
            fail("neutrality: nothing was posted, so the comparison is vacuous");
        if (without.solutions != with.solutions)
            fail("neutrality: the solution set changed");
        if (without.recursions != with.recursions)
            fail("neutrality: " + to_string(with.recursions) + " nodes against " + to_string(without.recursions) +
                " --- the inferred constraint changed what time-tabling permits, which means it is not implied");
        println(cerr, "neutrality: {} nodes either way", with.recursions);
    }

    // Budgets, and that they are counted rather than silent.
    {
        auto stats = make_shared<InferredDisjunctiveStats>();
        solve_family(3, 2, 6, Setup{.max_candidates = 0, .stats = stats}, nullopt);
        if (stats->cliques_posted != 0)
            fail("a zero candidate budget still posted a clique");
        if (stats->dropped_over_budget == 0)
            fail("a zero candidate budget dropped candidates without counting them");
    }

    // Two resources, each forbidding one pair, with no conflict between the
    // pairs: the conflict graph is two disjoint edges and every maximal clique
    // has two members. Nothing worth posting --- a pair is already kept apart by
    // the resource that witnesses it --- but the drops have to be counted, or
    // "found nothing" and "dropped everything" look the same.
    {
        auto stats = make_shared<InferredDisjunctiveStats>();
        Problem p;
        vector<IntegerVariableID> starts;
        for (int i = 0; i < 4; ++i)
            starts.push_back(p.create_integer_variable(0_i, 4_i));

        const vector<Integer> lengths(4, 2_i);
        p.post(Cumulative{starts, lengths, vector<Integer>{1_i, 1_i, 0_i, 0_i}, 1_i});
        p.post(Cumulative{starts, lengths, vector<Integer>{0_i, 0_i, 1_i, 1_i}, 1_i});
        p.add_presolver(InferredDisjunctive{stats});
        solve_with(p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return false; }}, nullopt);

        if (stats->conflicting_pairs != 2)
            fail("disjoint pairs: found " + to_string(stats->conflicting_pairs) + " conflicting pairs, not the two there are");
        if (stats->cliques_posted != 0)
            fail("disjoint pairs: a two-task clique was posted, which cannot infer anything the resource has not");
        if (stats->dropped_too_small != 2)
            fail("disjoint pairs: " + to_string(stats->dropped_too_small) + " undersized cliques counted, not the two dropped");
    }
    println(cerr, "budgets: candidate cap and minimum size both bite, and both are counted");

    // An optional-task donor is declined loudly rather than mis-derived.
    {
        auto stats = make_shared<InferredDisjunctiveStats>();
        Problem p;
        vector<IntegerVariableID> starts, presences;
        for (int i = 0; i < 3; ++i) {
            starts.push_back(p.create_integer_variable(0_i, 3_i));
            presences.push_back(p.create_integer_variable(0_i, 1_i));
        }
        vector<IntegerVariableID> lengths{constant_variable(2_i), constant_variable(2_i), constant_variable(2_i)},
            heights{constant_variable(1_i), constant_variable(1_i), constant_variable(1_i)};
        p.post(Cumulative{starts, lengths, heights, presences, constant_variable(1_i)});
        p.add_presolver(InferredDisjunctive{stats});
        solve_with(p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return false; }}, nullopt);

        if (stats->declined_optional != 1)
            fail("an optional-task donor was not declined");
        if (stats->cliques_posted != 0)
            fail("an optional-task donor was used anyway");
    }
    println(cerr, "an optional-task donor is declined");

    if (! proofs) {
        println(cerr, "veripb is not available, so the proof-level checks are skipped");
        return EXIT_SUCCESS;
    }

    // Nothing may have reached the OPB: the whole plan turns on an inferred
    // constraint being a derivation rather than a model axiom.
    {
        const string with = "inferred_disjunctive_opb_with", without = "inferred_disjunctive_opb_without";
        for (const auto & [name, presolve] : {std::pair{with, true}, std::pair{without, false}}) {
            Problem p;
            post_family(p, 3, 2, 6, Setup{.presolve = presolve});
            solve_with(
                p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return false; }}, make_optional<ProofOptions>(ProofFileNames{name}));
        }
        if (read_file(with + ".opb") != read_file(without + ".opb"))
            fail("the inferred constraint changed the OPB");
        for (const auto & name : {with, without})
            dispose_of_proof_files(name);
        println(cerr, "the OPB is untouched");
    }

    // And the markers say the clique derivation actually ran, per time point.
    {
        const string name = "inferred_disjunctive_markers";
        solve_family(3, 2, 5, Setup{}, make_optional(name), false);
        if (! run_veripb(name + ".opb", name + ".pbp"))
            fail("markers: veripb rejected the proof");
        auto proof = read_file(name + ".pbp");
        if (0 == count_occurrences(proof, "presolve disjunctive: inferred a clique"))
            fail("markers: no clique was recorded as inferred");
        if (0 == count_occurrences(proof, "presolve disjunctive clique at time"))
            fail("markers: no per-time clique derivation in the proof");
        println(cerr, "markers: {} per-time clique derivations", count_occurrences(proof, "presolve disjunctive clique at time"));
        dispose_of_proof_files(name);
    }

    return EXIT_SUCCESS;
}
