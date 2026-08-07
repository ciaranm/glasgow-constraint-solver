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
#include <gcs/constraints/linear.hh>
#include <gcs/presolvers/inferred_disjunctive.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <fstream>
#include <functional>
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
        InferredDisjunctiveMutation mutation = inferred_disjunctive_mutation::None{};
        shared_ptr<InferredDisjunctiveStats> stats = nullptr;

        /// Add a makespan variable, the `start_i + length <= makespan` rows
        /// that make it one, and minimise it --- so that a posted clique's
        /// total duration is not only reported but derived.
        bool minimise_makespan = false;
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

        optional<IntegerVariableID> makespan;
        if (setup.minimise_makespan) {
            makespan = p.create_integer_variable(0_i, Integer{horizon}, "makespan");
            for (const auto & start : starts)
                p.post(LinearGreaterThanEqual{WeightedSum{} + 1_i * *makespan + -1_i * start, Integer{length}});
            p.minimise(*makespan);
        }

        if (setup.presolve) {
            auto presolver = InferredDisjunctive{setup.stats};
            presolver.with_budgets(setup.max_candidates, setup.max_posted).with_minimum_clique_size(setup.min_clique_size);
            presolver.with_proof_mutation(setup.mutation);
            if (setup.inferred_rules)
                presolver.with_rules(*setup.inferred_rules);
            if (makespan)
                presolver.with_makespan(*makespan);
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
        // Sidorov's L, and the whole reason this fixture is unsatisfiable:
        // three tasks of length two must run one after another, so they need
        // six units, and the horizon supplies five. Asserting it here rather
        // than just the clique's size is what makes the reported bound a
        // checked number rather than an incidental one --- it is the number
        // the Pack / Pack-d cross-check compares against the paper.
        if (stats->largest_capacity_bound != 6_i)
            fail("reported a capacity bound of " + to_string(stats->largest_capacity_bound.raw_value) +
                ", not the six units three length-two tasks must serialise into");
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

    // The same six, derived rather than reported. With a makespan named, the
    // clique's total duration is pushed onto it at the root with a certificate,
    // and it is exactly the optimum here --- three length-two tasks that must
    // serialise finish at six and no sooner.
    {
        auto stats = make_shared<InferredDisjunctiveStats>();
        auto certified = solve_family(
            3, 2, 8, Setup{.stats = stats, .minimise_makespan = true}, proofs ? make_optional("inferred_disjunctive_makespan") : nullopt);

        if (stats->largest_capacity_bound != 6_i)
            fail("certified bound: reported an L of " + to_string(stats->largest_capacity_bound.raw_value) + ", not six");
        if (stats->certified_makespan_bound != 6_i)
            fail("certified bound: derived a makespan bound of " + to_string(stats->certified_makespan_bound.raw_value) +
                ", not the six the clique carries");

        // The same number with proofs off, or the solver is doing different
        // arithmetic depending on whether anyone is watching.
        auto unproved_stats = make_shared<InferredDisjunctiveStats>();
        solve_family(3, 2, 8, Setup{.stats = unproved_stats, .minimise_makespan = true}, nullopt);
        if (unproved_stats->certified_makespan_bound != stats->certified_makespan_bound)
            fail("certified bound: the bound differs with proofs off");

        println(cerr, "certified makespan bound: derived {} over {} nodes", stats->certified_makespan_bound.raw_value, certified.recursions);

        // And one more than the clique carries must be refused. The energy
        // argument itself is mutation-tested where it lives, in
        // makespan_energy; what this covers is *this* presolver's forwarding of
        // it --- the spec field, the links it fills in and the flag that
        // selects the corruption. A bound with slack in it verifies whatever it
        // concludes, so an honest derivation reaching a number the geometry
        // does not support would look exactly like this one. Six is the
        // optimum, so seven is infeasible and the margin is the required one.
        if (proofs) {
            const string name = "inferred_disjunctive_makespan_mutation";
            solve_family(3, 2, 8, Setup{.mutation = inferred_disjunctive_mutation::ClaimHigherMakespanBound{}, .minimise_makespan = true},
                make_optional(name), false);
            if (run_veripb(name + ".opb", name + ".pbp"))
                fail("veripb accepted a makespan bound one above what the clique carries");
            dispose_of_proof_files(name);
            println(cerr, "veripb rejected the higher-makespan mutation, as expected");
        }
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
        if (stats->dropped_over_candidate_budget == 0)
            fail("a zero candidate budget dropped candidates without counting them");
        if (stats->dropped_over_posting_budget != 0)
            fail("a zero candidate budget charged its drops to the posting budget");
        // Nothing posted has to mean no bound claimed: a stale capacity bound
        // would be a lower bound nobody derived.
        if (stats->largest_capacity_bound != 0_i)
            fail("posted no clique but still reported a capacity bound of " + to_string(stats->largest_capacity_bound.raw_value));
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

    /* Variable arguments, which are a restriction on a *task* rather than on a
     * resource. Three tasks of length two, pairwise conflicting on three
     * resources exactly as the family above, but with two things that family
     * cannot say: the capacity is one shared variable over [3, 5] rather than a
     * posted constant, and a fourth task carries a variable height.
     *
     * Both are the derived side of the same reduction. The capacity's rows are
     * argued against five, the weakest it can be, which every witness's
     * at-most-one is recovered from --- and five is not one less than a power of
     * two, so the order atom really does come back with a coefficient to pay
     * off. The fourth task's terms in those rows are the bits of a linearised
     * contribution rather than `height x active`, so the reduction has to take
     * all of them out before the at-most-one program weakens over what is left.
     *
     * A demand of three conflicts with another three at any capacity up to five,
     * so the clique is the same one; the fourth task demands one, which does not
     * conflict with three at five but does at three, so it stays a decision the
     * search makes rather than one the presolver has taken.
     *
     * Its height being a variable no longer keeps it out of the graph: it is
     * converted to the demand it is guaranteed to make, which is one. What the
     * reduction still has to do is the capacity, and the fourth task's terms
     * are still the bits of a linearised contribution --- converted rather than
     * weakened away now, which is a different `pol` over the same bits.
     */
    {
        const int k = 3, length = 2, horizon = 6, latest = horizon - length;
        auto stats = make_shared<InferredDisjunctiveStats>();

        Problem p;
        vector<IntegerVariableID> starts;
        for (int i = 0; i <= k; ++i)
            starts.push_back(p.create_integer_variable(0_i, Integer{latest}, "s" + to_string(i)));
        auto capacity = p.create_integer_variable(3_i, 5_i, "capacity");
        auto varying = p.create_integer_variable(1_i, 1_i, "h3");

        vector<IntegerVariableID> lengths(static_cast<size_t>(k) + 1, constant_variable(Integer{length}));
        for (int r = 0; r < k; ++r) {
            vector<IntegerVariableID> heights(static_cast<size_t>(k) + 1, constant_variable(0_i));
            for (int i = 0; i < k; ++i)
                for (int j = i + 1; j < k; ++j)
                    if ((i + j) % k == r) {
                        heights[static_cast<size_t>(i)] = constant_variable(3_i);
                        heights[static_cast<size_t>(j)] = constant_variable(3_i);
                    }
            heights[static_cast<size_t>(k)] = varying;
            p.post(Cumulative{starts, lengths, heights, capacity});
        }
        p.add_presolver(InferredDisjunctive{stats});

        set<vector<int>> solutions;
        solve_with(p, SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
            vector<int> solution;
            for (const auto & v : starts)
                solution.push_back(s(v).raw_value);
            solution.push_back(s(capacity).raw_value);
            solutions.insert(move(solution));
            return true;
        }},
            proofs ? make_optional<ProofOptions>(ProofFileNames{"inferred_disjunctive_variable_arguments"}) : nullopt);
        if (proofs)
            verify_proof_and_clean_up("inferred_disjunctive_variable_arguments");

        if (stats->cliques_posted != 1)
            fail("a clique was not posted over resources with variable arguments");
        if (stats->converted_heights != static_cast<size_t>(k))
            fail("the variable-height task was not converted on every resource");
        if (stats->resources_with_set_aside_tasks != 0)
            fail("a variable height set its task aside, rather than being converted to its guaranteed demand");
        if (stats->declined_irreducible_capacity != 0)
            fail("a resource was declined for a task's variable height, which is now a conversion");

        // Brute force over the same model: the fourth task takes part or not
        // depending on the capacity, which is why it is in the tuple.
        set<vector<int>> expected;
        vector<int> assignment(static_cast<size_t>(k) + 2, 0);
        std::function<auto(size_t)->void> enumerate = [&](size_t at) {
            if (at == assignment.size()) {
                for (int r = 0; r < k; ++r)
                    for (int t = 0; t < horizon; ++t) {
                        int load = 0;
                        for (int i = 0; i <= k; ++i) {
                            if (assignment[static_cast<size_t>(i)] > t || t >= assignment[static_cast<size_t>(i)] + length)
                                continue;
                            if (i == k)
                                load += 1;
                            else
                                for (int a = 0; a < k; ++a)
                                    for (int b = a + 1; b < k; ++b)
                                        if ((a + b) % k == r && (i == a || i == b))
                                            load += 3;
                        }
                        if (load > assignment.back())
                            return;
                    }
                expected.insert(assignment);
                return;
            }
            auto lo = at == assignment.size() - 1 ? 3 : 0;
            auto hi = at == assignment.size() - 1 ? 5 : latest;
            for (auto v = lo; v <= hi; ++v) {
                assignment[at] = v;
                enumerate(at + 1);
            }
        };
        enumerate(0);

        if (expected != solutions)
            fail("variable-argument solutions do not match brute force");
        println(cerr, "variable arguments: clique posted, {} solutions", solutions.size());
    }

    /* A clique that exists only because a variable height was converted. Three
     * tasks, pairwise conflicting on the three resources `(i + j) mod 3` covers
     * between them at a demand of three against a capacity of five --- except
     * that the third task's demand is a *variable* over [3, 4], so on the two
     * resources it appears on its terms are the bits of a linearised
     * contribution rather than a coefficient on its activity flag.
     *
     * Set aside, as it would have been, that task has no conflicts at all: one
     * pair is left, the clique is of two, and the minimum size of three refuses
     * it. Converted to the demand it is guaranteed to make --- three, its lower
     * bound --- all three pairs conflict and the clique is the whole family. So
     * `conflicting_pairs` is the measure here: three with the conversion, one
     * without.
     */
    {
        const int k = 3, length = 2, horizon = 6, latest = horizon - length;
        auto stats = make_shared<InferredDisjunctiveStats>();

        Problem p;
        vector<IntegerVariableID> starts;
        for (int i = 0; i < k; ++i)
            starts.push_back(p.create_integer_variable(0_i, Integer{latest}, "s" + to_string(i)));
        auto varying = p.create_integer_variable(3_i, 4_i, "h2");

        vector<IntegerVariableID> lengths(static_cast<size_t>(k), constant_variable(Integer{length}));
        for (int r = 0; r < k; ++r) {
            vector<IntegerVariableID> heights(static_cast<size_t>(k), constant_variable(0_i));
            for (int i = 0; i < k; ++i)
                for (int j = i + 1; j < k; ++j)
                    if ((i + j) % k == r) {
                        // The last task's demand is the variable one wherever it
                        // appears; everyone else's is the constant three.
                        heights[static_cast<size_t>(i)] = i == k - 1 ? varying : constant_variable(3_i);
                        heights[static_cast<size_t>(j)] = j == k - 1 ? varying : constant_variable(3_i);
                    }
            p.post(Cumulative{starts, lengths, heights, constant_variable(5_i)});
        }
        p.add_presolver(InferredDisjunctive{stats});

        set<vector<int>> solutions;
        solve_with(p, SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
            vector<int> solution;
            for (const auto & v : starts)
                solution.push_back(s(v).raw_value);
            solution.push_back(s(varying).raw_value);
            solutions.insert(move(solution));
            return true;
        }},
            proofs ? make_optional<ProofOptions>(ProofFileNames{"inferred_disjunctive_converted_height"}) : nullopt);
        if (proofs)
            verify_proof_and_clean_up("inferred_disjunctive_converted_height");

        if (stats->conflicting_pairs != 3)
            fail("found " + to_string(stats->conflicting_pairs) +
                " conflicting pairs, not the three the conversion reaches --- one is what setting the task aside would give");
        if (stats->cliques_posted != 1)
            fail("no clique was posted over a converted height");
        if (stats->clique_members_posted != static_cast<size_t>(k))
            fail("the converted task did not join the clique");
        if (stats->converted_heights != 2)
            fail("the variable height was converted on " + to_string(stats->converted_heights) + " resources, not the two it appears on");
        if (stats->resources_with_set_aside_tasks != 0)
            fail("a variable height set its task aside rather than converting");

        // Brute force: no two tasks may overlap, whatever the third's demand
        // turns out to be, since three plus anything at least three is over five.
        set<vector<int>> expected;
        vector<int> assignment(static_cast<size_t>(k) + 1, 0);
        std::function<auto(size_t)->void> enumerate = [&](size_t at) {
            if (at == assignment.size()) {
                for (int i = 0; i < k; ++i)
                    for (int j = i + 1; j < k; ++j)
                        if (assignment[static_cast<size_t>(i)] < assignment[static_cast<size_t>(j)] + length &&
                            assignment[static_cast<size_t>(j)] < assignment[static_cast<size_t>(i)] + length)
                            return;
                expected.insert(assignment);
                return;
            }
            auto lo = at == assignment.size() - 1 ? 3 : 0;
            auto hi = at == assignment.size() - 1 ? 4 : latest;
            for (auto v = lo; v <= hi; ++v) {
                assignment[at] = v;
                enumerate(at + 1);
            }
        };
        enumerate(0);

        if (expected != solutions)
            fail("converted-height solutions do not match brute force");
        println(cerr, "converted height: {} conflicting pairs, a clique of {}", stats->conflicting_pairs, stats->clique_members_posted);
    }

    /* A variable duration, which unlike a variable height is not a restriction
     * at all. A conflict is a statement about demands, and a clique's rows say
     * nothing about how long anything runs for --- so what used to cost a task
     * its place in the conflict graph now costs it nothing, provided its donor
     * published the line a pin of its `after` goes through.
     *
     * Four tasks, pairwise conflicting, one capacity-one resource per pair, and
     * the last one's duration a variable. The clique is a clique of *four*:
     * three is what it would be with that task set aside, and the difference is
     * the whole point.
     *
     * A resource per pair rather than the four this used to share the six pairs
     * out between, because any such sharing puts two disjoint pairs on one
     * resource --- and a capacity-one resource holding every member of the
     * clique *is* the clique, which the presolver now declines to infer again
     * rather than reporting as its own. This fixture was measuring that decline
     * without saying so.
     */
    {
        const int k = 4, length = 2, horizon = 9, latest = horizon - length;
        auto stats = make_shared<InferredDisjunctiveStats>();

        Problem p;
        vector<IntegerVariableID> starts;
        for (int i = 0; i < k; ++i)
            starts.push_back(p.create_integer_variable(0_i, Integer{latest}, "s" + to_string(i)));
        // Only the last, so that what the fixture counts is one task joining a
        // clique it could not have joined, rather than a clique of tasks none
        // of which the energy rules could have counted anyway.
        auto varying = p.create_integer_variable(Integer{length}, Integer{length + 1}, "l3");

        vector<IntegerVariableID> lengths(static_cast<size_t>(k), constant_variable(Integer{length}));
        lengths.back() = varying;
        for (int i = 0; i < k; ++i)
            for (int j = i + 1; j < k; ++j) {
                vector<IntegerVariableID> heights(static_cast<size_t>(k), constant_variable(0_i));
                heights[static_cast<size_t>(i)] = constant_variable(1_i);
                heights[static_cast<size_t>(j)] = constant_variable(1_i);
                p.post(Cumulative{starts, lengths, heights, constant_variable(1_i)});
            }
        p.add_presolver(InferredDisjunctive{stats});

        set<vector<int>> solutions;
        solve_with(p, SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
            vector<int> solution;
            for (const auto & v : starts)
                solution.push_back(s(v).raw_value);
            solution.push_back(s(varying).raw_value);
            solutions.insert(move(solution));
            return true;
        }},
            proofs ? make_optional<ProofOptions>(ProofFileNames{"inferred_disjunctive_variable_length"}) : nullopt);
        if (proofs)
            verify_proof_and_clean_up("inferred_disjunctive_variable_length");

        if (stats->cliques_posted != 1)
            fail("a clique was not posted over a resource with a variable duration");
        if (stats->clique_members_posted != static_cast<size_t>(k))
            fail("the variable-duration task did not join the clique, which is the whole gain");
        if (stats->resources_with_set_aside_tasks != 0)
            fail("a variable duration set its task aside, which is what the published end proxy is there to avoid");

        // Brute force over the same model: no two tasks may overlap, and the
        // last one's duration is part of the assignment.
        set<vector<int>> expected;
        vector<int> assignment(static_cast<size_t>(k) + 1, 0);
        auto duration = [&](int i) { return i == k - 1 ? assignment.back() : length; };
        std::function<auto(size_t)->void> enumerate = [&](size_t at) {
            if (at == assignment.size()) {
                for (int i = 0; i < k; ++i)
                    for (int j = i + 1; j < k; ++j)
                        if (assignment[static_cast<size_t>(i)] < assignment[static_cast<size_t>(j)] + duration(j) &&
                            assignment[static_cast<size_t>(j)] < assignment[static_cast<size_t>(i)] + duration(i))
                            return;
                expected.insert(assignment);
                return;
            }
            auto lo = at == assignment.size() - 1 ? length : 0;
            auto hi = at == assignment.size() - 1 ? length + 1 : latest;
            for (auto v = lo; v <= hi; ++v) {
                assignment[at] = v;
                enumerate(at + 1);
            }
        };
        enumerate(0);

        if (expected != solutions)
            fail("variable-duration solutions do not match brute force");
        println(cerr, "variable duration: a clique of {} tasks, {} solutions", stats->clique_members_posted, solutions.size());
    }

    /* A clique one posted capacity-one resource already contains, which is that
     * resource's own constraint and not an inference. Posting it would add a
     * propagator that can say nothing the donor does not, and --- the part that
     * matters --- reporting its total duration as `largest_capacity_bound`
     * would report a number the model came with. Sidorov's L4 discards
     * constraints a model row dominates, and this is that test at unit
     * coefficients.
     */
    {
        auto stats = make_shared<InferredDisjunctiveStats>();
        Problem p;
        vector<IntegerVariableID> starts;
        for (int i = 0; i < 3; ++i)
            starts.push_back(p.create_integer_variable(0_i, 5_i, "s" + to_string(i)));
        p.post(Cumulative{starts, vector<Integer>(3, 2_i), vector<Integer>(3, 1_i), 1_i});
        p.add_presolver(InferredDisjunctive{stats});

        set<vector<int>> solutions;
        solve_with(p, SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
            vector<int> solution;
            for (const auto & v : starts)
                solution.push_back(s(v).raw_value);
            solutions.insert(move(solution));
            return true;
        }},
            proofs ? make_optional<ProofOptions>(ProofFileNames{"inferred_disjunctive_dominated"}) : nullopt);
        if (proofs)
            verify_proof_and_clean_up("inferred_disjunctive_dominated");

        if (stats->conflicting_pairs != 3)
            fail("dominated clique: " + to_string(stats->conflicting_pairs) + " conflicting pairs, not the three");
        if (stats->cliques_found != 1)
            fail("dominated clique: the clique was not even found, so the drop below means nothing");
        if (stats->dropped_dominated != 1)
            fail("dominated clique: " + to_string(stats->dropped_dominated) + " cliques dropped as dominated, not the one");
        if (stats->cliques_posted != 0)
            fail("dominated clique: a clique a posted resource already contains was posted anyway");
        if (stats->largest_capacity_bound != 0_i)
            fail("dominated clique: reported a capacity bound of " + to_string(stats->largest_capacity_bound.raw_value) +
                ", which the model already contained");
        if (solutions != expected_solutions(3, 2, 7))
            fail("dominated clique: solutions do not match brute force");
        println(cerr, "dominated clique: found and dropped, and no bound claimed for it");
    }

    /* A witnessing pair *both* of whose demands strictly exceed the capacity,
     * which is the one case where recovering the at-most-one does not land on
     * an at-most-one. The margin is then bigger than either demand, so the
     * divisor is the larger demand rather than the margin, and the bound comes
     * back as zero: a line saying neither task may run rather than that at most
     * one may. Stronger, so the induction that folds the pairs still advances
     * and the syntactic pin still accepts --- but for a different reason than
     * the one written beside the call, which is why this is worth a fixture.
     *
     * It can only be an infeasible model, and that is not a fixture design
     * choice: a task demanding more than a resource has can never be active at
     * any time point, and a mandatory task of non-zero length must be active
     * somewhere. So what this checks is the arithmetic and the pin --- `pol`
     * steps are checked exactly whatever the model says, and an implication
     * check is syntactic --- and *not* the enumeration, which an unsatisfiable
     * model would agree with however the derivation had gone.
     */
    {
        auto stats = make_shared<InferredDisjunctiveStats>();
        Problem p;
        vector<IntegerVariableID> starts;
        for (int i = 0; i < 3; ++i)
            starts.push_back(p.create_integer_variable(0_i, 3_i, "s" + to_string(i)));
        const vector<Integer> lengths(3, 2_i);

        // Three over two, so the margin is four and the larger demand is three.
        p.post(Cumulative{starts, lengths, vector<Integer>{3_i, 3_i, 0_i}, 2_i});
        // And the other two pairs witnessed ordinarily, so that the clique is
        // of three and the fold has something to fold.
        p.post(Cumulative{starts, lengths, vector<Integer>{1_i, 0_i, 1_i}, 1_i});
        p.post(Cumulative{starts, lengths, vector<Integer>{0_i, 1_i, 1_i}, 1_i});
        p.add_presolver(InferredDisjunctive{stats});

        bool any_solution = false;
        solve_with(p, SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
            any_solution = true;
            return true;
        }},
            proofs ? make_optional<ProofOptions>(ProofFileNames{"inferred_disjunctive_pair_both_over"}) : nullopt);
        if (proofs)
            verify_proof_and_clean_up("inferred_disjunctive_pair_both_over");

        if (any_solution)
            fail("both demands over the capacity: a task that cannot run anywhere was scheduled");
        if (stats->cliques_posted != 1 || stats->clique_members_posted != 3)
            fail("both demands over the capacity: posted " + to_string(stats->cliques_posted) + " cliques over " +
                to_string(stats->clique_members_posted) + " members, not the one clique of three");
        println(cerr, "both demands over the capacity: the clique is still recovered and the pin still accepts");
    }

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

    /* Mutations of the assembled certificate.
     *
     * The pieces have their own, and those cover the pieces. What is left is
     * the assembly, and it needs a fixture with a *camouflage* task: a fourth
     * task on a resource of capacity two, where every pairwise demand sums to
     * exactly two. Compatible, but only just --- which is what an off-by-one in
     * the conflict test would get wrong, and what IncludeNonConflicting forces.
     */
    {
        auto camouflage = [](Problem & p, const Setup & setup) {
            vector<IntegerVariableID> starts;
            for (int i = 0; i < 4; ++i)
                starts.push_back(p.create_integer_variable(0_i, 3_i, "s" + to_string(i)));

            const vector<Integer> lengths(4, 2_i);
            // The three-task cross-resource family, over the first three.
            p.post(Cumulative{starts, lengths, vector<Integer>{0_i, 1_i, 1_i, 0_i}, 1_i});
            p.post(Cumulative{starts, lengths, vector<Integer>{1_i, 1_i, 0_i, 0_i}, 1_i});
            p.post(Cumulative{starts, lengths, vector<Integer>{1_i, 0_i, 1_i, 0_i}, 1_i});
            // And a resource all four share, where any two of them fit exactly.
            p.post(Cumulative{starts, lengths, vector<Integer>{1_i, 1_i, 1_i, 1_i}, 2_i});

            auto presolver = InferredDisjunctive{setup.stats};
            presolver.with_proof_mutation(setup.mutation);
            p.add_presolver(presolver);
            return starts;
        };

        // Honestly, task three joins no clique: it is compatible with every
        // one of the others, by exactly one unit.
        {
            auto stats = make_shared<InferredDisjunctiveStats>();
            Problem p;
            camouflage(p, Setup{.stats = stats});
            solve_with(p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return false; }},
                make_optional<ProofOptions>(ProofFileNames{"inferred_disjunctive_camouflage"}));
            if (stats->cliques_posted != 1 || stats->clique_members_posted != 3)
                fail("camouflage: posted " + to_string(stats->cliques_posted) + " cliques over " + to_string(stats->clique_members_posted) +
                    " members, not the one clique of three");
            verify_proof_and_clean_up("inferred_disjunctive_camouflage");
            println(cerr, "camouflage: the compatible task stayed out of the clique, and the proof verifies");
        }

        for (const auto & [what, mutation] :
            {std::pair<string, InferredDisjunctiveMutation>{"rhs zero", inferred_disjunctive_mutation::ClaimRhsZero{}},
                std::pair<string, InferredDisjunctiveMutation>{"wrong task bridged", inferred_disjunctive_mutation::BridgeWrongTask{}},
                std::pair<string, InferredDisjunctiveMutation>{"non-conflicting member", inferred_disjunctive_mutation::IncludeNonConflicting{}}}) {
            const string name = "inferred_disjunctive_mutation";
            Problem p;
            camouflage(p, Setup{.mutation = mutation});
            solve_with(
                p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return true; }}, make_optional<ProofOptions>(ProofFileNames{name}));

            if (run_veripb(name + ".opb", name + ".pbp"))
                fail("veripb accepted the " + what + " mutation, so the honest certificate has slack in it");
            println(cerr, "veripb rejected the {} mutation, as expected", what);
            dispose_of_proof_files(name);
        }
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

        // And the working is deleted rather than left in the database. Every
        // line a time point emits except its pin exists only to reach that pin,
        // and at Top there are order k squared of them per time point that
        // nothing ever cites again (issue #666). The presolve prefix is
        // everything up to the last clique marker, so counting deletions there
        // asks about this presolver rather than about the search.
        auto prefix = proof.substr(0, proof.rfind("presolve disjunctive: inferred a clique"));
        auto derivations = count_occurrences(prefix, "presolve disjunctive clique at time");
        auto deletions = count_occurrences(prefix, "del ");
        if (deletions < derivations)
            fail("proof size: " + to_string(derivations) + " per-time derivations left " + to_string(deletions) +
                " deletions behind, so their scaffolding is still live");
        println(cerr, "proof size: {} deletions over {} per-time derivations, so only the pins outlive them", deletions, derivations);
        dispose_of_proof_files(name);
    }

    return EXIT_SUCCESS;
}
