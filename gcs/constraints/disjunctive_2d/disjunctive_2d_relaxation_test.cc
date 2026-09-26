/* The cumulative relaxation for Disjunctive2D (#972), and its certificate.
 *
 * The rule projects the rectangles onto one axis and time-tables the
 * Cumulative that projection implies: rectangle i becomes a task with start
 * pos_i and duration size_i on the time axis, of height its size on the
 * resource axis, on a resource whose capacity is the extent the set is
 * confined to there.
 *
 * Every fixture here comes with a *control* --- the same instance with the
 * rule off --- because a green suite says nothing about a rule nothing else
 * fires. The fixtures are built so that the pairwise rule is silent on them by
 * construction: no rectangle has a mandatory part on the resource axis, so
 * there is no mandatory box to overlap and no blocker to be pushed away from,
 * which is exactly the gap the relaxation fills.
 *
 * The proof side is the interesting half. The capacity row the argument needs
 * is not in the OPB and never will be, so it is derived per firing: each
 * pair's two time-axis disjuncts are refuted from the certificate's own
 * literals, what is left of their 4-way separation clause separates them on
 * the resource axis, and a comparator network sorts the set and telescopes.
 * Those clauses are derived rather than model rows, so they carry the guard,
 * which is what assume_with_guarded_separations is for.
 */

#include <gcs/constraints/disjunctive_2d.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <fstream>
#include <iostream>
#include <optional>
#include <random>
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
#endif

using std::cerr;
using std::ifstream;
using std::make_optional;
using std::mt19937;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
using std::string;
using std::to_string;
using std::uniform_int_distribution;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::println;
#else
using fmt::println;
#endif

using namespace gcs;
using namespace gcs::innards;

namespace
{
    struct Instance
    {
        vector<pair<int, int>> x_ranges, y_ranges;
        vector<int> widths, heights;
        /// Unit squares free across the whole bounded range in x, each with
        /// the y range given, posted after the rest: a time axis wider than
        /// an int (#1083). Brute force cannot enumerate them, so only `probe`
        /// takes an instance that has any.
        vector<pair<int, int>> wide_y_ranges = {};
    };

    /// What every rule under test writes into the proof when it fires: the
    /// relaxation's rungs, and the projection's capacity rows, which are only
    /// ever derived because some rule of Cumulative's cited one.
    const string firing_marker = "disjunctive2d cumulative ";

    auto fail(const string & message) -> void
    {
        println(cerr, "disjunctive_2d_relaxation_test: {}", message);
        exit(EXIT_FAILURE);
    }

    auto post(Problem & p, const Instance & inst, Disjunctive2DRules rules,
        Disjunctive2DProofMutation mutation = disjunctive_2d_proof_mutation::None{}) -> pair<vector<IntegerVariableID>, vector<IntegerVariableID>>
    {
        vector<IntegerVariableID> xs, ys;
        vector<Integer> widths, heights;
        for (const auto & [lo, hi] : inst.x_ranges)
            xs.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));
        for (const auto & [lo, hi] : inst.y_ranges)
            ys.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));
        for (auto w : inst.widths)
            widths.push_back(Integer{w});
        for (auto h : inst.heights)
            heights.push_back(Integer{h});
        for (const auto & [lo, hi] : inst.wide_y_ranges) {
            xs.push_back(p.create_integer_variable(Integer::min_bounded_value(), Integer::max_bounded_value()));
            ys.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));
            widths.push_back(1_i);
            heights.push_back(1_i);
        }
        p.post(Disjunctive2D{xs, ys, widths, heights}.with_rules(rules).with_proof_mutation(mutation));
        return {xs, ys};
    }

    /// As `post`, but through the optional-rectangle constructor: each entry of
    /// `presences` is either a constant (0 or 1) or nullopt for a fresh {0, 1}
    /// variable, and the variables made are returned so they can be enumerated.
    auto post_optional(Problem & p, const Instance & inst, Disjunctive2DRules rules, const vector<optional<int>> & presences)
        -> std::tuple<vector<IntegerVariableID>, vector<IntegerVariableID>, vector<IntegerVariableID>>
    {
        vector<IntegerVariableID> xs, ys, widths, heights, pres, pres_vars;
        for (const auto & [lo, hi] : inst.x_ranges)
            xs.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));
        for (const auto & [lo, hi] : inst.y_ranges)
            ys.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));
        for (auto w : inst.widths)
            widths.push_back(ConstantIntegerVariableID{Integer{w}});
        for (auto h : inst.heights)
            heights.push_back(ConstantIntegerVariableID{Integer{h}});
        for (const auto & pr : presences)
            if (pr)
                pres.push_back(ConstantIntegerVariableID{Integer{*pr}});
            else {
                auto v = p.create_integer_variable(0_i, 1_i);
                pres.push_back(v);
                pres_vars.push_back(v);
            }
        p.post(Disjunctive2D{xs, ys, widths, heights, pres}.with_rules(rules));
        return {xs, ys, pres_vars};
    }

    auto count_markers(const string & basename, const string & marker) -> int
    {
        ifstream f{basename + ".pbp"};
        string line;
        auto count = 0;
        while (getline(f, line))
            if (line.find(marker) != string::npos)
                ++count;
        return count;
    }

    /// What root propagation alone came to. Satisfiability is no use as a
    /// control for the conflict fixture --- an instance the rule refutes is
    /// unsatisfiable with the rule off too, just found by searching --- so what
    /// separates the rules is whether the root closes, and what the pushed
    /// rectangle's bounds are when it does not.
    struct Probe
    {
        bool refuted_at_root = false;
        bool satisfiable = false;
        int markers = 0;
        vector<pair<Integer, Integer>> root_x, root_y;
    };

    /// `root_only` stops at the first node, which is what makes a comparison
    /// between two rule sets mean something: the test harness branches
    /// randomly and reseeds every run, so node counts are not reproducible and
    /// what the rules did at the root is.
    auto probe(const Instance & inst, Disjunctive2DRules rules, const optional<string> & proof_name, bool root_only = false) -> Probe
    {
        Problem p;
        auto [xs, ys] = post(p, inst, rules);
        Probe result;
        auto reached_a_node = false;
        solve_with(p,
            SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                               result.satisfiable = true;
                               return false;
                           },
                .trace = [&](const CurrentState & s) -> bool {
                    // The first node is the root, after propagation: what the
                    // rule did without any branching. The search runs on, so
                    // that satisfiability means something too.
                    if (! reached_a_node)
                        for (size_t i = 0; i < xs.size(); ++i) {
                            result.root_x.emplace_back(s.lower_bound(xs[i]), s.upper_bound(xs[i]));
                            result.root_y.emplace_back(s.lower_bound(ys[i]), s.upper_bound(ys[i]));
                        }
                    reached_a_node = true;
                    return ! root_only;
                }},
            proof_name ? make_optional<ProofOptions>(ProofFileNames{*proof_name}) : nullopt);
        result.refuted_at_root = ! reached_a_node && ! result.satisfiable;
        if (proof_name)
            result.markers = count_markers(*proof_name, firing_marker);
        return result;
    }

    auto verify(const string & name) -> bool
    {
        return gcs::test_innards::run_veripb(name + ".opb", name + ".pbp");
    }

    /// Enumerate, and check against brute force: the rule may prune, so long as
    /// it prunes nothing that satisfies the constraint. This is the check a
    /// conflict fixture cannot make, and the one a wrong capacity or a wrong
    /// window would fail. Returns how many times the rule fired, because a run
    /// whose firings are zero has checked nothing about it, however many
    /// solutions it agreed on.
    auto enumerate_and_check(const Instance & inst, Disjunctive2DRules rules, const optional<string> & proof_name) -> int
    {
        if (! inst.wide_y_ranges.empty())
            fail("an instance with a wide rectangle cannot be enumerated by brute force");
        auto n = inst.x_ranges.size();
        auto is_satisfying = [&](const vector<int> & vals) {
            for (size_t i = 0; i < n; ++i)
                for (size_t j = i + 1; j < n; ++j) {
                    auto xi = vals[i], yi = vals[n + i], xj = vals[j], yj = vals[n + j];
                    if (! (xi + inst.widths[i] <= xj || xj + inst.widths[j] <= xi || yi + inst.heights[i] <= yj || yj + inst.heights[j] <= yi))
                        return false;
                }
            return true;
        };

        auto all_ranges = inst.x_ranges;
        all_ranges.insert(all_ranges.end(), inst.y_ranges.begin(), inst.y_ranges.end());
        set<vector<int>> expected, actual;
        gcs::test_innards::build_expected(expected, is_satisfying, all_ranges);

        Problem p;
        auto [xs, ys] = post(p, inst, rules);
        vector<IntegerVariableID> all_vars = xs;
        all_vars.insert(all_vars.end(), ys.begin(), ys.end());
        gcs::test_innards::solve_for_tests(p, proof_name, actual, std::tuple{all_vars});

        // A capped run holds only some of the solutions, so it cannot say the
        // rule lost none of them --- which is the whole point of enumerating.
        if (gcs::test_innards::last_run_truncated())
            fail("an enumeration was stopped early by a cap, so it checked no completeness");

        auto markers = proof_name ? count_markers(*proof_name, firing_marker) : 0;
        gcs::test_innards::check_results(proof_name, expected, actual);
        return markers;
    }

    /// A non-strict instance with *two* zero-size escapes in one firing, which
    /// is the shape that made the escapes have to be pinned as well as guarded:
    /// with one, the closing RUP still reaches `~escape` by bit arithmetic;
    /// with two it does not. A variable width has a mandatory part only where
    /// its origin is fixed, lb(width) being one; the third rectangle is three
    /// wide and reaches the same time from anywhere in its domain. Seven units
    /// of height then have to fit in five.
    /// `share_width` gives the two of them one width *variable* between them,
    /// so the guard names the same literal twice and each rectangle still gets
    /// an escape flag of its own. Nothing merges those terms on the way out, so
    /// this asks whether the checker's own normalisation is being leaned on.
    auto post_two_escapes(Problem & p, Disjunctive2DRules rules, Disjunctive2DProofMutation mutation, bool share_width = false) -> void
    {
        vector<IntegerVariableID> xs, ys, widths, heights;
        auto shared = p.create_integer_variable(1_i, 3_i);
        for (auto i = 0; i < 3; ++i) {
            xs.push_back(i == 2 ? p.create_integer_variable(0_i, 2_i) : p.create_integer_variable(2_i, 2_i));
            ys.push_back(p.create_integer_variable(0_i, 2_i));
            heights.push_back(ConstantIntegerVariableID{i == 2 ? 3_i : 2_i});
            widths.push_back(i == 2 ? IntegerVariableID{ConstantIntegerVariableID{3_i}}
                    : share_width   ? shared
                                    : IntegerVariableID{p.create_integer_variable(1_i, 3_i)});
        }
        p.post(Disjunctive2D{xs, ys, widths, heights}.with_strict(false).with_rules(rules).with_proof_mutation(mutation));
    }

    /// One instance of a random sweep's family; see run_random_sweep for what
    /// each shape is for.
    auto random_instance(mt19937 & rand, int shape) -> Instance
    {
        // The overload check is conflict-only and fires on area, and a
        // narrow domain gives a rectangle a mandatory part the pairwise rule
        // then refutes just as well. So its sweep packs four or five
        // rectangles, mostly two by two, into a box four by four, each
        // free to go anywhere in it --- which gives none of them a
        // mandatory part on either axis, and often more area than the box.
        // shape 2 is edge-finding's: the same, but six wide with each x
        // range at its own offset, since a rule about a rectangle with one
        // end inside a window needs windows that do not contain everything.
        auto dense = shape != 0;
        auto n = dense ? uniform_int_distribution<int>{4, 5}(rand) : uniform_int_distribution<int>{2, 4}(rand);
        Instance inst;
        for (auto i = 0; i < n; ++i) {
            if (dense) {
                auto size = [&]() { return uniform_int_distribution<int>{0, 3}(rand) == 0 ? 1 : 2; };
                auto w = size(), h = size();
                inst.widths.push_back(w);
                inst.heights.push_back(h);
                if (shape == 2)
                    inst.x_ranges.emplace_back(0, 6 - w);
                else
                    inst.x_ranges.emplace_back(0, 4 - w);
                inst.y_ranges.emplace_back(0, 4 - h);
            }
            else {
                inst.widths.push_back(uniform_int_distribution<int>{1, 3}(rand));
                inst.heights.push_back(uniform_int_distribution<int>{1, 3}(rand));
                inst.x_ranges.emplace_back(0, uniform_int_distribution<int>{0, 3}(rand));
                inst.y_ranges.emplace_back(0, uniform_int_distribution<int>{0, 3}(rand));
            }
        }
        // Edge-finding's shape: all but one or two of the rectangles are
        // confined, two wide, to a four-wide window at a random offset in a
        // box six wide, and the rest are free across it --- the fixtures'
        // family, since a push needs a window its contents nearly fill and
        // a rectangle with one end inside it.
        if (shape == 2) {
            auto free = uniform_int_distribution<int>{1, 2}(rand);
            auto offset = uniform_int_distribution<int>{0, 2}(rand);
            for (auto i = 0; i + free < n; ++i) {
                inst.widths[i] = 2;
                inst.x_ranges[i] = {offset, offset + 2};
            }
            for (auto i = n - free; i < n; ++i) {
                inst.heights[i] = uniform_int_distribution<int>{2, 4}(rand);
                inst.y_ranges[i] = {0, 4 - inst.heights[i]};
            }
        }
        return inst;
    }

    /// Random instances, which is where a certificate bug that a hand-built
    /// fixture is too symmetric to expose shows up. Each one enumerates every
    /// solution and verifies its own proof; the sweep as a whole has to have
    /// fired the rule and to have pruned something, or it has checked a
    /// propagator that was never asked anything.
    ///
    /// Its own lane, and nothing else runs in it: the two lanes run
    /// concurrently under a parallel ctest from one directory, so a sweep that
    /// also ran the fixtures would race the fixture lane over their proof files
    /// (issue #562, and #961 for what that looks like).
    auto run_random_sweep(int search_instances, bool proofs, Disjunctive2DRules with, Disjunctive2DRules without, const string & stem, int shape)
        -> void
    {
        mt19937 rand;
        rand.seed(1234);
        auto total_markers = 0;
        auto pruned_somewhere = false;
        for (auto instance = 0; instance < search_instances; ++instance) {
            // -1 alternates between the two dense families, for a rule set
            // wide enough to want both: overload on area, and pushes out of a
            // window its contents nearly fill.
            auto inst = random_instance(rand, shape == -1 ? 1 + instance % 2 : shape);
            auto name = stem + to_string(instance);
            println(
                cerr, "disjunctive2d relaxation random {}: xr={} yr={} w={} h={}", instance, inst.x_ranges, inst.y_ranges, inst.widths, inst.heights);
            total_markers += enumerate_and_check(inst, with, proofs ? make_optional(name) : nullopt);

            // And the control, at the root where it is reproducible: whatever
            // the rule concluded there, the pairwise rule alone must not have,
            // on at least one of these instances. The solutions themselves are
            // already known to agree, check_results having compared each
            // enumeration against brute force.
            auto ruled = probe(inst, with, nullopt, true), control = probe(inst, without, nullopt, true);
            if (ruled.refuted_at_root != control.refuted_at_root || ruled.root_x != control.root_x || ruled.root_y != control.root_y)
                pruned_somewhere = true;
        }
        println(cerr, "disjunctive2d relaxation: {} firings over {} random instances", total_markers, search_instances);
        if (proofs && total_markers == 0)
            fail("the random sweep never fired the rule");
        if (! pruned_somewhere)
            fail("the random sweep never pruned anything the pairwise rule did not");
    }
}

auto main(int argc, char * argv[]) -> int
{
    gcs::test_innards::establish_and_announce_seed(argc, argv);

    auto proofs = gcs::test_innards::can_run_veripb();
    auto search_instances = 0;
    optional<Disjunctive2DProofMutation> mutation;
    // The overload check on the relaxation (#984) rather than its time-table
    // rung: selects the rule the sweep and the mutation lanes run.
    auto overload = false;
    // And edge-finding on the relaxation, likewise.
    auto edge_finding = false;
    // And time-table edge-finding on the relaxation.
    auto ttef = false;
    // And Cumulative's own propagator on each projection (#973), with every
    // one of its rules on.
    auto projection = false;
    // With a mutation: run it over this many instances of the sweep's family
    // and report which ones VeriPB rejects, to find a fixture on which it is
    // load-bearing. A development tool, not a lane.
    auto survey = 0;
    string mutation_basename = "disjunctive_2d_relaxation_mutation";
    for (auto a = 1; a < argc; ++a) {
        string arg = argv[a];
        if (arg == "--search" && a + 1 < argc)
            search_instances = std::stoi(argv[++a]);
        else if (arg == "--mutate=emit_nothing")
            mutation = disjunctive_2d_proof_mutation::EmitNothing{};
        else if (arg == "--mutate=skip_refutation")
            mutation = disjunctive_2d_proof_mutation::SkipOneRefutation{};
        else if (arg == "--mutate=skip_guard_weakening")
            mutation = disjunctive_2d_proof_mutation::SkipGuardWeakening{};
        else if (arg == "--mutate=skip_escape_pins")
            mutation = disjunctive_2d_proof_mutation::SkipEscapePins{};
        else if (arg == "--mutate=overload_emit_nothing") {
            mutation = disjunctive_2d_proof_mutation::EmitNothing{};
            overload = true;
        }
        else if (arg == "--mutate=overload_skip_energy") {
            mutation = disjunctive_2d_proof_mutation::OverloadSkipEnergy{};
            overload = true;
        }
        else if (arg == "--mutate=overload_skip_row") {
            mutation = disjunctive_2d_proof_mutation::OverloadSkipRow{};
            overload = true;
        }
        else if (arg == "--mutate=edge_finding_one_too_far") {
            mutation = disjunctive_2d_proof_mutation::EdgeFindingOneTooFar{};
            edge_finding = true;
        }
        else if (arg == "--mutate=edge_finding_drop_pushed") {
            mutation = disjunctive_2d_proof_mutation::EdgeFindingDropPushed{};
            edge_finding = true;
        }
        else if (arg == "--overload")
            overload = true;
        else if (arg == "--edge-finding")
            edge_finding = true;
        else if (arg == "--ttef")
            ttef = true;
        else if (arg == "--survey" && a + 1 < argc)
            survey = std::stoi(argv[++a]);
        else if (arg == "--mutate=ttef_one_too_far") {
            mutation = disjunctive_2d_proof_mutation::EdgeFindingOneTooFar{};
            ttef = true;
        }
        else if (arg == "--mutate=ttef_drop_pushed") {
            mutation = disjunctive_2d_proof_mutation::EdgeFindingDropPushed{};
            ttef = true;
        }
        else if (arg == "--mutate=ttef_drop_pins") {
            mutation = disjunctive_2d_proof_mutation::TimeTableEdgeFindingDropPins{};
            ttef = true;
        }
        else if (arg == "--projection")
            projection = true;
        else if (arg == "--mutate=projection_row_too_strong") {
            mutation = disjunctive_2d_proof_mutation::ProjectionRowTooStrong{};
            projection = true;
        }
        else if (arg == "--mutate=projection_skip_bridge") {
            mutation = disjunctive_2d_proof_mutation::ProjectionSkipBridge{};
            projection = true;
        }
        else if (arg == "--mutate=projection_skip_refutations") {
            mutation = disjunctive_2d_proof_mutation::ProjectionSkipRefutations{};
            projection = true;
        }
        else if (arg == "--proof-files-basename" && a + 1 < argc)
            mutation_basename = argv[++a];
    }

    // Every rule Cumulative has, for the projection's sweep and enumerations:
    // what is being checked is the rows and flags the projection supplies, and
    // each rule cites them differently.
    const CumulativeRules every_cumulative_rule{.elastic_overload = true,
        .knapsack_overload = true,
        .edge_finding = true,
        .time_table_edge_finding = true,
        .energetic_edge_finding = true,
        .not_first_not_last = true,
        .not_first_not_last_published = true};

    const Disjunctive2DRules with = projection ? Disjunctive2DRules{.cumulative_projection = every_cumulative_rule}
        : ttef                                 ? Disjunctive2DRules{.relaxation_time_table_edge_finding = true}
        : edge_finding                         ? Disjunctive2DRules{.relaxation_edge_finding = true}
        : overload                             ? Disjunctive2DRules{.relaxation_overload = true}
                                               : Disjunctive2DRules{.cumulative_relaxation = true};

    // The edge-finding fixtures. Three squares of two confined to x in [0, 2]
    // fill 12 of the 16 units of area the window [0, 4) has under a y extent
    // of four; a fourth rectangle, two wide and four tall and free in x over
    // [0, 6], would add 4 per column it overlaps, so it cannot start before
    // 3. Nothing has a mandatory x part, so time-tabling is silent.
    const Instance ef_lb{{{0, 2}, {0, 2}, {0, 2}, {0, 6}}, {{0, 2}, {0, 2}, {0, 2}, {0, 0}}, {2, 2, 2, 2}, {2, 2, 2, 4}};
    // The mirror: the three squares in [4, 8) and the tall one ending inside
    // it, so it cannot start after 3.
    const Instance ef_ub{{{4, 6}, {4, 6}, {4, 6}, {0, 6}}, {{0, 2}, {0, 2}, {0, 2}, {0, 0}}, {2, 2, 2, 2}, {2, 2, 2, 4}};

    // The TTEF fixtures. As `ef_lb` with the third square replaced by a
    // rectangle three wide over x in [1, 3]: no window edge-finding looks at
    // both contains it and gives a push, but its mandatory part [3, 4) is
    // inside [0, 4). That is 8 units contained plus 2 of profile, so the tall
    // one cannot start before 3 --- and edge-finding alone, seeing only the
    // 8, cannot push at all. (See check_push below for where it ends up.)
    const Instance ttef_lb{{{0, 2}, {0, 2}, {1, 3}, {0, 6}}, {{0, 2}, {0, 2}, {0, 2}, {0, 0}}, {2, 2, 3, 2}, {2, 2, 2, 4}};
    // Its mirror in x, in a box eight wide.
    const Instance ttef_ub{{{4, 6}, {4, 6}, {2, 4}, {0, 6}}, {{0, 2}, {0, 2}, {0, 2}, {0, 0}}, {2, 2, 3, 2}, {2, 2, 2, 4}};
    // Found by `--mutate=ttef_drop_pushed --survey 200`: an instance on which
    // the pushed rectangle's own energy is load-bearing. On `ttef_lb` it is
    // not --- unit propagation closes the push without it --- so that lane
    // runs here instead. (Dropping the pins is rejected on none of the 199
    // instances the survey fired on: propagation derives every pin from the
    // reason's bounds through the flag's reverse row, so no lane pins them.)
    const Instance ttef_pushed_matters{{{2, 4}, {2, 4}, {2, 4}, {0, 4}}, {{0, 3}, {0, 2}, {0, 2}, {0, 0}}, {2, 2, 2, 2}, {1, 2, 2, 4}};
    const Disjunctive2DRules without{};

    // The overload fixture: seven squares of two in a box five by five, 28
    // units of area in 25. Every origin ranges over [0, 3], so no square has
    // a mandatory part on either axis and neither the pairwise rule nor the
    // relaxation's time-table rung has anything to go on.
    const Instance area{vector<pair<int, int>>(7, {0, 3}), vector<pair<int, int>>(7, {0, 3}), vector<int>(7, 2), vector<int>(7, 2)};

    if (search_instances > 0) {
        // A stem per rule: the two sweep lanes run concurrently from one
        // directory, and a shared proof name is the race #961 was.
        run_random_sweep(search_instances, proofs, with, without,
            projection         ? "disjunctive_2d_projection_search_"
                : ttef         ? "disjunctive_2d_relaxation_ttef_search_"
                : edge_finding ? "disjunctive_2d_relaxation_edge_finding_search_"
                : overload     ? "disjunctive_2d_relaxation_overload_search_"
                               : "disjunctive_2d_relaxation_search_",
            projection                   ? -1
                : (ttef || edge_finding) ? 2
                : overload               ? 1
                                         : 0);
        return EXIT_SUCCESS;
    }

    // The conflict fixture. Three rectangles three wide with every x in
    // [0, 2], so each one's mandatory x part is [2, 3) and all three share the
    // time 2. Their y positions run over [0, 5] and each is three tall, so the
    // window holding them is eight and they need nine.
    //
    // No rectangle has a mandatory *y* part (latest start 5 is past earliest
    // end 3), so no mandatory box overlaps another and no pair has a blocker
    // to be pushed away from: the pairwise rule sees nothing here at all.
    const Instance sharp{{{0, 2}, {0, 2}, {0, 2}}, {{0, 5}, {0, 5}, {0, 5}}, {3, 3, 3}, {3, 3, 3}};

    // Mutation mode: emit one deliberately corrupted proof and stop, for
    // run_test_and_expect_verify_failure.bash to hand to veripb.
    //
    // `sharp` has no zero-size escapes in it, so the escape-pin mutation runs
    // on a non-strict instance with *two* of them instead: one escape the
    // closing RUP can still reach by bit arithmetic, and a lane on one would
    // pass with the pins gone.
    if (mutation && survey > 0) {
        mt19937 rand;
        rand.seed(1234);
        auto rejected = 0, fired = 0;
        for (auto k = 0; k < survey; ++k) {
            auto inst = random_instance(rand, projection ? 1 + k % 2 : (edge_finding || ttef) ? 2 : overload ? 1 : 0);
            auto name = mutation_basename + "_survey";
            Problem p;
            post(p, inst, with, *mutation);
            solve_with(p, SolveCallbacks{}, make_optional<ProofOptions>(ProofFileNames{name}));
            if (count_markers(name, firing_marker) == 0)
                continue;
            ++fired;
            if (! verify(name)) {
                ++rejected;
                println(cerr, "survey: rejected on xr={} yr={} w={} h={}", inst.x_ranges, inst.y_ranges, inst.widths, inst.heights);
            }
        }
        println(cerr, "survey: {} of {} instances where the rule fired rejected the mutation", rejected, fired);
        return EXIT_SUCCESS;
    }

    if (mutation) {
        Problem p;
        if (std::holds_alternative<disjunctive_2d_proof_mutation::SkipEscapePins>(*mutation))
            post_two_escapes(p, with, *mutation);
        else if (ttef)
            post(p, std::holds_alternative<disjunctive_2d_proof_mutation::EdgeFindingDropPushed>(*mutation) ? ttef_pushed_matters : ttef_lb, with,
                *mutation);
        else if (edge_finding)
            post(p, ef_lb, with, *mutation);
        else if (overload || projection)
            post(p, area, with, *mutation);
        else
            post(p, sharp, with, *mutation);
        solve_with(p, SolveCallbacks{}, make_optional<ProofOptions>(ProofFileNames{mutation_basename}));
        if (count_markers(mutation_basename, firing_marker) == 0)
            fail("mutation mode: the rule never fired, so the proof has nothing corrupted in it");
        println(cerr, "wrote a deliberately corrupted proof to {}.pbp", mutation_basename);
        return EXIT_SUCCESS;
    }

    {
        auto name = "disjunctive_2d_relaxation_sharp";
        auto result = probe(sharp, with, proofs ? make_optional(string{name}) : nullopt);
        if (result.satisfiable)
            fail("sharp: a solution was reported, but nine units of height do not fit in eight");
        if (! result.refuted_at_root)
            fail("sharp: the rule did not close the root");
        if (proofs && result.markers < 1)
            fail("sharp: no relaxation marker in the proof, so something else refuted it");
        if (proofs && ! verify(name))
            fail("sharp: veripb rejected the relaxation certificate");

        auto control = probe(sharp, without, nullopt);
        if (control.refuted_at_root)
            fail("sharp: the root closed with the rule off, so the fixture says nothing about the rule");
    }

    // The margin of one: a unit more room on the resource axis and the
    // rectangles fit, so the refutation above is not a technicality.
    {
        auto name = "disjunctive_2d_relaxation_loose";
        Instance loose = sharp;
        loose.y_ranges = {{0, 6}, {0, 6}, {0, 6}};
        auto result = probe(loose, with, proofs ? make_optional(string{name}) : nullopt);
        if (result.refuted_at_root)
            fail("loose: the root closed, but nine units of height fit in exactly nine");
        if (! result.satisfiable)
            fail("loose: no solution, but three three-tall rectangles stack in nine");
        if (proofs && result.markers != 0)
            fail("loose: an overflow was claimed where the work fits");
        if (proofs && ! verify(name))
            fail("loose: veripb rejected the proof");
    }

    // The push fixture. Two rectangles are pinned at x = 2 and one wide, so
    // both occupy the time 2; the third is three wide with x in [0, 6]. All
    // three are three tall with y in [0, 5], so the window is eight and the
    // two pinned ones already use six of it. The third cannot occupy time 2 as
    // well, and at three wide that rules out every origin from 0 to 2.
    //
    // Again nothing has a mandatory y part, so the pairwise rule is silent.
    const Instance push{{{2, 2}, {2, 2}, {0, 6}}, {{0, 5}, {0, 5}, {0, 5}}, {1, 1, 3}, {3, 3, 3}};
    {
        auto name = "disjunctive_2d_relaxation_push";
        auto result = probe(push, with, proofs ? make_optional(string{name}) : nullopt);
        if (result.refuted_at_root)
            fail("push: the root closed, but the third rectangle fits to the right of the other two");
        if (result.root_x.size() != 3)
            fail("push: no root node was traced");
        if (result.root_x[2].first < 3_i)
            fail("push: the third rectangle's origin was left at " + to_string(result.root_x[2].first.raw_value) + ", expected at least 3");
        if (proofs && result.markers < 1)
            fail("push: no relaxation marker in the proof");
        if (proofs && ! verify(name))
            fail("push: veripb rejected the push certificate");

        auto control = probe(push, without, nullopt);
        if (control.root_x.size() != 3)
            fail("push: the control traced no root node");
        if (control.root_x[2].first >= 3_i)
            fail("push: the bound moved with the rule off, so the fixture says nothing about the rule");
    }

    // The same push with the blocked time at the very start of the domain, so
    // that the pushed rectangle's own "it occupies t" lower bound --- stated
    // tightly at `t - width + 1` --- lands *below* its domain. The literal is
    // then one the encoding has no order atom for, which is a different path
    // through the certificate and one the fixture above does not take.
    {
        auto name = "disjunctive_2d_relaxation_push_at_zero";
        const Instance at_zero{{{0, 0}, {0, 0}, {0, 6}}, {{0, 5}, {0, 5}, {0, 5}}, {1, 1, 3}, {3, 3, 3}};
        auto result = probe(at_zero, with, proofs ? make_optional(string{name}) : nullopt);
        if (result.root_x.size() != 3)
            fail("push_at_zero: no root node was traced");
        if (result.root_x[2].first < 1_i)
            fail("push_at_zero: the third rectangle's origin was left at " + to_string(result.root_x[2].first.raw_value) + ", expected at least 1");
        if (proofs && ! verify(name))
            fail("push_at_zero: veripb rejected the certificate");

        auto control = probe(at_zero, without, nullopt);
        if (control.root_x[2].first >= 1_i)
            fail("push_at_zero: the bound moved with the rule off, so the fixture says nothing about the rule");
    }

    // The mirror: the same instance transposed, so the rule has to find it with
    // y playing the part of time. The two rules run over the same code with the
    // axes swapped, and a fixture that only ever exercises one of them would not
    // notice the other being wired up wrongly.
    {
        auto name = "disjunctive_2d_relaxation_push_transposed";
        Instance transposed{push.y_ranges, push.x_ranges, push.heights, push.widths};
        auto result = probe(transposed, with, proofs ? make_optional(string{name}) : nullopt);
        if (result.root_y.size() != 3)
            fail("transposed: no root node was traced");
        if (result.root_y[2].first < 3_i)
            fail("transposed: the third rectangle's origin was left at " + to_string(result.root_y[2].first.raw_value));
        if (proofs && ! verify(name))
            fail("transposed: veripb rejected the transposed push certificate");
    }

    // The honest counterpart of the escape-pin mutation lane: the same two
    // escapes in one firing, undamaged. Without both the pin and the guard this
    // is what VeriPB rejects, so a lane that only ran the corrupted version
    // could be rejecting it for some unrelated reason.
    {
        auto name = "disjunctive_2d_relaxation_two_escapes";
        Problem p;
        post_two_escapes(p, with, disjunctive_2d_proof_mutation::None{});
        auto reached_a_node = false, satisfiable = false;
        solve_with(p,
            SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                               satisfiable = true;
                               return false;
                           },
                .trace = [&](const CurrentState &) -> bool {
                    reached_a_node = true;
                    return false;
                }},
            proofs ? make_optional<ProofOptions>(ProofFileNames{name}) : nullopt);
        if (satisfiable || reached_a_node)
            fail("two_escapes: seven units of height do not fit in five, and the rule should close the root");
        if (proofs && count_markers(name, firing_marker) < 1)
            fail("two_escapes: no relaxation marker, so the escapes were never in a guard");
        if (proofs && ! verify(name))
            fail("two_escapes: veripb rejected the certificate");
    }

    // The same, with one width variable shared between the two of them, so the
    // guard names its literal twice over. Repeated terms in a `rup` line are
    // the checker's business rather than ours, and this is what says we are not
    // relying on that quietly.
    {
        auto name = "disjunctive_2d_relaxation_shared_width";
        Problem p;
        post_two_escapes(p, with, disjunctive_2d_proof_mutation::None{}, true);
        auto reached_a_node = false, satisfiable = false;
        solve_with(p,
            SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                               satisfiable = true;
                               return false;
                           },
                .trace = [&](const CurrentState &) -> bool {
                    reached_a_node = true;
                    return false;
                }},
            proofs ? make_optional<ProofOptions>(ProofFileNames{name}) : nullopt);
        if (satisfiable || reached_a_node)
            fail("shared_width: seven units of height do not fit in five, and the rule should close the root");
        if (proofs && count_markers(name, firing_marker) < 1)
            fail("shared_width: no relaxation marker");
        if (proofs && ! verify(name))
            fail("shared_width: veripb rejected the certificate");
    }

    // Variable widths, which is a different route through the certificate: the
    // mandatory part is over lb(width), so each refutation has a size term to
    // cancel as well, and the reason carries the "width is at least this much"
    // literal that does it. In non-strict mode a variable size also puts a
    // zero-size escape in the separation clause, which the guard then has to
    // carry as a fact of its own --- the rectangle is not zero-sized --- so
    // both modes are run.
    //
    // Heights stay constant: that is the axis the network sorts on, and it
    // pins a duration. Such a rectangle therefore takes part with x as time and
    // not with y, which is itself worth exercising.
    for (auto strict : {true, false}) {
        auto name = string{"disjunctive_2d_relaxation_varwidth_"} + (strict ? "strict" : "nonstrict");
        vector<pair<int, int>> x_ranges{{0, 2}, {0, 2}, {0, 2}}, y_ranges{{0, 4}, {0, 4}, {0, 4}}, w_specs{{1, 3}, {1, 3}, {3, 3}};
        vector<int> heights{2, 2, 3};

        // Enumerated in this order: xs, ys, then the variable widths.
        auto is_satisfying = [&](const vector<int> & vals) {
            vector<int> w{vals[6], vals[7], 3};
            for (size_t i = 0; i < 3; ++i)
                for (size_t j = i + 1; j < 3; ++j) {
                    auto xi = vals[i], yi = vals[3 + i], xj = vals[j], yj = vals[3 + j];
                    if (! strict && (w[i] == 0 || heights[i] == 0 || w[j] == 0 || heights[j] == 0))
                        continue;
                    if (! (xi + w[i] <= xj || xj + w[j] <= xi || yi + heights[i] <= yj || yj + heights[j] <= yi))
                        return false;
                }
            return true;
        };
        auto all_ranges = x_ranges;
        all_ranges.insert(all_ranges.end(), y_ranges.begin(), y_ranges.end());
        all_ranges.push_back(w_specs[0]);
        all_ranges.push_back(w_specs[1]);

        set<vector<int>> expected, actual;
        gcs::test_innards::build_expected(expected, is_satisfying, all_ranges);

        Problem p;
        vector<IntegerVariableID> xs, ys, widths, all_vars;
        for (const auto & [lo, hi] : x_ranges)
            xs.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));
        for (const auto & [lo, hi] : y_ranges)
            ys.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));
        for (const auto & [lo, hi] : w_specs)
            widths.push_back(lo == hi ? IntegerVariableID{ConstantIntegerVariableID{Integer{lo}}}
                                      : IntegerVariableID{p.create_integer_variable(Integer{lo}, Integer{hi})});
        vector<IntegerVariableID> heights_id;
        for (auto h : heights)
            heights_id.push_back(ConstantIntegerVariableID{Integer{h}});
        p.post(Disjunctive2D{xs, ys, widths, heights_id}.with_strict(strict).with_rules(with));

        all_vars = xs;
        all_vars.insert(all_vars.end(), ys.begin(), ys.end());
        all_vars.push_back(widths[0]);
        all_vars.push_back(widths[1]);
        gcs::test_innards::solve_for_tests(p, proofs ? make_optional(name) : nullopt, actual, std::tuple{all_vars});
        if (gcs::test_innards::last_run_truncated())
            fail(name + ": a cap fired, so the enumeration checked no completeness");
        auto markers = proofs ? count_markers(name, firing_marker) : 0;
        gcs::test_innards::check_results(proofs ? make_optional(name) : nullopt, expected, actual);
        if (proofs && markers == 0)
            fail(name + ": the rule never fired, so this route through the certificate went unchecked");
    }

    // --- optional rectangles, from both sides ---------------------------
    //
    // The rule decides membership from bounds alone, so an optional rectangle
    // whose presence is undecided must take no part: counting its height would
    // make the overflow conclusion prune placements that need it absent. A
    // constant-present one must still take part, or the rule quietly does
    // nothing on the optional form. The guard in prepare() has to get both
    // right, and each fixture below pins one direction: deleting the guard
    // turns the first red, and tightening it to exclude every optional
    // rectangle turns the other two red. An on-and-off enumeration of the
    // constant-present case would pin neither --- leaving a rectangle out only
    // ever weakens propagation, so the solution set is the same either way ---
    // which is why those two assert that the rule *fires*.

    // Undecided. Two unconditionally present rectangles two tall share the
    // time 2 on a window five high, so four fits; a third, three tall and
    // optional, would make seven. Every solution has the third one absent, so
    // counting it refutes the root and loses all six of them.
    {
        auto name = "disjunctive_2d_relaxation_optional_undecided";
        const Instance inst{{{2, 2}, {2, 2}, {2, 2}}, {{0, 2}, {0, 2}, {0, 2}}, {1, 1, 1}, {2, 2, 3}};
        auto is_satisfying = [&](const vector<int> & vals) {
            // y0, y1, y2, present2. Every x is 2 and every width 1, so no pair
            // can separate on the time axis: it is the resource axis or nothing.
            vector<int> y{vals[0], vals[1], vals[2]};
            vector<bool> here{true, true, vals[3] == 1};
            for (size_t i = 0; i < 3; ++i)
                for (size_t j = i + 1; j < 3; ++j)
                    if (here[i] && here[j] && ! (y[i] + inst.heights[i] <= y[j] || y[j] + inst.heights[j] <= y[i]))
                        return false;
            return true;
        };
        set<vector<int>> expected, actual;
        gcs::test_innards::build_expected(expected, is_satisfying, vector<pair<int, int>>{{0, 2}, {0, 2}, {0, 2}, {0, 1}});
        if (expected.empty())
            fail("optional_undecided: the fixture has no solutions, so it could not lose any");

        Problem p;
        auto [xs, ys, pres] = post_optional(p, inst, with, {1, 1, nullopt});
        vector<IntegerVariableID> all_vars{ys[0], ys[1], ys[2], pres.at(0)};
        gcs::test_innards::solve_for_tests(p, proofs ? make_optional(string{name}) : nullopt, actual, std::tuple{all_vars});
        if (gcs::test_innards::last_run_truncated())
            fail("optional_undecided: a cap fired, so the enumeration checked no completeness");
        gcs::test_innards::check_results(proofs ? make_optional(string{name}) : nullopt, expected, actual);
    }

    // Constant-present, and the rule has to fire. `sharp` with every presence
    // the constant 1 is the same instance, and its root must close by the
    // relaxation alone --- which it could not if the constant-present
    // rectangles were being left out.
    {
        auto name = "disjunctive_2d_relaxation_optional_constant_sharp";
        auto root_closes = [&](Disjunctive2DRules rules, const optional<string> & proof_name) -> pair<bool, int> {
            Problem p;
            (void)post_optional(p, sharp, rules, {1, 1, 1});
            auto reached_a_node = false, satisfiable = false;
            solve_with(p,
                SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                                   satisfiable = true;
                                   return false;
                               },
                    .trace = [&](const CurrentState &) -> bool {
                        reached_a_node = true;
                        return false;
                    }},
                proof_name ? make_optional<ProofOptions>(ProofFileNames{*proof_name}) : nullopt);
            return {! reached_a_node && ! satisfiable, proof_name ? count_markers(*proof_name, firing_marker) : 0};
        };
        auto [closed, markers] = root_closes(with, proofs ? make_optional(string{name}) : nullopt);
        if (! closed)
            fail("optional_constant_sharp: the root did not close, so constant-present rectangles are being left out of the rule");
        if (proofs && markers < 1)
            fail("optional_constant_sharp: no relaxation marker, so something else closed the root");
        if (proofs && ! verify(name))
            fail("optional_constant_sharp: veripb rejected the certificate");
        if (root_closes(without, nullopt).first)
            fail("optional_constant_sharp: the root closed with the rule off, so the fixture says nothing about the rule");
    }

    // Constant-present, enumerated: `small` with every presence the constant
    // 1, against brute force, and with the rule required to have fired. The
    // enumeration is what says taking part is *sound* for such a rectangle;
    // the firing is what says it took part at all.
    {
        auto name = "disjunctive_2d_relaxation_optional_constant_enumerate";
        const Instance small{{{0, 3}, {0, 3}, {0, 3}}, {{0, 4}, {0, 4}, {0, 4}}, {2, 2, 2}, {2, 2, 2}};
        auto n = small.x_ranges.size();
        auto is_satisfying = [&](const vector<int> & vals) {
            for (size_t i = 0; i < n; ++i)
                for (size_t j = i + 1; j < n; ++j) {
                    auto xi = vals[i], yi = vals[n + i], xj = vals[j], yj = vals[n + j];
                    if (! (xi + small.widths[i] <= xj || xj + small.widths[j] <= xi || yi + small.heights[i] <= yj || yj + small.heights[j] <= yi))
                        return false;
                }
            return true;
        };
        auto all_ranges = small.x_ranges;
        all_ranges.insert(all_ranges.end(), small.y_ranges.begin(), small.y_ranges.end());
        set<vector<int>> expected, actual;
        gcs::test_innards::build_expected(expected, is_satisfying, all_ranges);

        Problem p;
        auto [xs, ys, pres] = post_optional(p, small, with, {1, 1, 1});
        vector<IntegerVariableID> all_vars = xs;
        all_vars.insert(all_vars.end(), ys.begin(), ys.end());
        gcs::test_innards::solve_for_tests(p, proofs ? make_optional(string{name}) : nullopt, actual, std::tuple{all_vars});
        if (gcs::test_innards::last_run_truncated())
            fail("optional_constant_enumerate: a cap fired, so the enumeration checked no completeness");
        auto markers = proofs ? count_markers(name, firing_marker) : 0;
        gcs::test_innards::check_results(proofs ? make_optional(string{name}) : nullopt, expected, actual);
        if (proofs && markers == 0)
            fail("optional_constant_enumerate: the rule never fired, so constant-present rectangles are being left out");
    }

    // Rectangles sharing a position handle take no part in the rule (their
    // facts would be the same literal twice in one guard), so turning it on
    // must leave such a model exactly as it was. Nothing here fires; what is
    // being checked is that asking does not break it.
    {
        auto name = "disjunctive_2d_relaxation_dup";
        vector<pair<int, int>> ranges{{0, 2}, {0, 3}, {0, 3}};
        auto is_satisfying = [&](const vector<int> & vals) {
            // Two rectangles at the same x, two tall and two wide, plus a third
            // whose x is its own.
            vector<int> x{vals[0], vals[0]}, y{vals[1], vals[2]};
            return x[0] + 2 <= x[1] || x[1] + 2 <= x[0] || y[0] + 2 <= y[1] || y[1] + 2 <= y[0];
        };
        set<vector<int>> expected, actual;
        gcs::test_innards::build_expected(expected, is_satisfying, ranges);

        Problem p;
        auto shared_x = p.create_integer_variable(0_i, 2_i);
        auto y0 = p.create_integer_variable(0_i, 3_i), y1 = p.create_integer_variable(0_i, 3_i);
        p.post(Disjunctive2D{
            vector<IntegerVariableID>{shared_x, shared_x}, vector<IntegerVariableID>{y0, y1}, vector<Integer>{2_i, 2_i}, vector<Integer>{2_i, 2_i}}
                .with_rules(with));
        vector<IntegerVariableID> all_vars{shared_x, y0, y1};
        gcs::test_innards::solve_for_tests(p, proofs ? make_optional(string{name}) : nullopt, actual, std::tuple{all_vars});
        gcs::test_innards::check_results(proofs ? make_optional(string{name}) : nullopt, expected, actual);
    }

    // Soundness, which is what a conflict fixture cannot check: enumerate a
    // small instance with the rule on and compare against brute force. A wrong
    // window or a wrong capacity prunes a solution here rather than merely
    // failing to verify.
    {
        const Instance small{{{0, 3}, {0, 3}, {0, 3}}, {{0, 4}, {0, 4}, {0, 4}}, {2, 2, 2}, {2, 2, 2}};
        auto markers = enumerate_and_check(small, with, proofs ? make_optional(string{"disjunctive_2d_relaxation_enumerate"}) : nullopt);
        if (proofs && markers == 0)
            fail("enumerate: the rule never fired, so agreeing with brute force says nothing about it");
    }

    // --- the overload check on the relaxation (#984) ---------------------
    //
    // Everything below is about Disjunctive2DRules::relaxation_overload alone,
    // so the controls are "that rule off" and not "the time-table rung off".
    if (! overload && ! edge_finding && ! ttef) {
        const Disjunctive2DRules overload_on{.relaxation_overload = true};
        auto closes = [&](const Instance & inst, Disjunctive2DRules rules, const optional<string> & name) -> pair<bool, int> {
            auto result = probe(inst, rules, name);
            return {result.refuted_at_root, name ? count_markers(*name, "disjunctive2d cumulative relaxation overload") : 0};
        };

        {
            auto name = "disjunctive_2d_relaxation_overload_area";
            auto [closed, markers] = closes(area, overload_on, proofs ? make_optional(string{name}) : nullopt);
            if (! closed)
                fail("overload_area: the root did not close, but 28 units of area do not fit in 25");
            if (proofs && markers < 1)
                fail("overload_area: no overload marker, so something else closed the root");
            if (proofs && ! verify(name))
                fail("overload_area: veripb rejected the overload certificate");
            if (closes(area, Disjunctive2DRules{.cumulative_relaxation = true}, nullopt).first)
                fail("overload_area: the time-table rung closed the root too, so the fixture says nothing about the overload check");
        }

        // The margin: four squares of two in four by four fill it exactly.
        {
            auto name = "disjunctive_2d_relaxation_overload_exact";
            const Instance exact{vector<pair<int, int>>(4, {0, 2}), vector<pair<int, int>>(4, {0, 2}), vector<int>(4, 2), vector<int>(4, 2)};
            auto result = probe(exact, overload_on, proofs ? make_optional(string{name}) : nullopt);
            if (result.refuted_at_root || ! result.satisfiable)
                fail("overload_exact: four squares of two tile four by four");
            // Not "no marker": the search goes on past the root, and once some
            // squares are placed the rest do overload the windows left, so the
            // rule rightly fires below the root. What it must not do is close
            // the root, or lose the tiling.
            if (proofs && ! verify(name))
                fail("overload_exact: veripb rejected the proof");
        }

        // Only the y projection overloads. Four squares confined to y in [0, 1]
        // put 16 units of area in a y window of three against an x extent of
        // five; a fifth, up at y in [3, 4], makes the whole box six tall, so on
        // the x projection 20 units sit in 30 and nothing fires. The two axes
        // run over the same code with the roles swapped, and this is what says
        // the swap is wired up right.
        {
            auto name = "disjunctive_2d_relaxation_overload_y_only";
            const Instance y_only{vector<pair<int, int>>(5, {0, 3}), {{0, 1}, {0, 1}, {0, 1}, {0, 1}, {3, 4}}, vector<int>(5, 2), vector<int>(5, 2)};
            auto [closed, markers] = closes(y_only, overload_on, proofs ? make_optional(string{name}) : nullopt);
            if (! closed)
                fail("overload_y_only: the root did not close");
            if (proofs && count_markers(name, "disjunctive2d cumulative relaxation overload axis=1") < 1)
                fail("overload_y_only: no y-axis overload marker");
            if (proofs && count_markers(name, "disjunctive2d cumulative relaxation overload axis=0") != 0)
                fail("overload_y_only: the x projection claimed an overload it does not have");
            if (proofs && ! verify(name))
                fail("overload_y_only: veripb rejected the certificate");
            if (closes(y_only, without, nullopt).first)
                fail("overload_y_only: the root closed with the rule off");
        }

        // Soundness by enumeration against brute force, with the rule firing.
        {
            // Four squares of two tiling four by four exactly: satisfiable, and
            // so tight that any placement below the root leaves windows the
            // rest overload, whichever way the reseeded search branches.
            const Instance small{vector<pair<int, int>>(4, {0, 2}), vector<pair<int, int>>(4, {0, 2}), vector<int>(4, 2), vector<int>(4, 2)};
            // Counted by enumerate_and_check itself, which disposes of the proof:
            // the overload marker shares the relaxation's prefix.
            auto markers =
                enumerate_and_check(small, overload_on, proofs ? make_optional(string{"disjunctive_2d_relaxation_overload_enumerate"}) : nullopt);
            if (proofs && markers == 0)
                fail("overload_enumerate: the rule never fired, so agreeing with brute force says nothing about it");
        }
    }

    // --- edge-finding on the relaxation (#984) ---------------------------
    if (! overload && ! edge_finding && ! ttef) {
        const Disjunctive2DRules ef_on{.relaxation_edge_finding = true};
        const Disjunctive2DRules ef_off{.cumulative_relaxation = true, .relaxation_overload = true};
        auto check_push = [&](const Instance & inst, const string & name, bool lower, Integer expected) {
            auto result = probe(inst, ef_on, proofs ? make_optional(name) : nullopt);
            if (result.root_x.size() != 4)
                fail(name + ": no root node was traced");
            auto got = lower ? result.root_x[3].first : result.root_x[3].second;
            if (got != expected)
                fail(name + ": the tall rectangle's " + (lower ? "lower" : "upper") + " bound is " + to_string(got.raw_value) + ", expected " +
                    to_string(expected.raw_value));
            if (proofs && count_markers(name, "disjunctive2d cumulative relaxation edge-finding") < 1)
                fail(name + ": no edge-finding marker, so something else made the push");
            if (proofs && ! verify(name))
                fail(name + ": veripb rejected the edge-finding certificate");
            if (! result.satisfiable)
                fail(name + ": the fixture is satisfiable, but no solution was found");
            auto control = probe(inst, ef_off, nullopt);
            auto control_bound = lower ? control.root_x[3].first : control.root_x[3].second;
            if (control_bound == expected)
                fail(name + ": the bound moved with edge-finding off, so the fixture says nothing about it");
        };
        check_push(ef_lb, "disjunctive_2d_relaxation_edge_finding_lb", true, 3_i);
        check_push(ef_ub, "disjunctive_2d_relaxation_edge_finding_ub", false, 3_i);

        {
            auto markers =
                enumerate_and_check(ef_lb, ef_on, proofs ? make_optional(string{"disjunctive_2d_relaxation_edge_finding_enumerate"}) : nullopt);
            if (proofs && markers == 0)
                fail("edge_finding_enumerate: the rule never fired");
        }
    }

    // --- time-table edge-finding on the relaxation (#984) ----------------
    if (! overload && ! edge_finding && ! ttef) {
        const Disjunctive2DRules ttef_on{.relaxation_time_table_edge_finding = true};
        const Disjunctive2DRules ttef_off{.cumulative_relaxation = true, .relaxation_overload = true, .relaxation_edge_finding = true};
        auto check_push = [&](const Instance & inst, const string & name, bool lower, Integer expected) {
            auto result = probe(inst, ttef_on, proofs ? make_optional(name) : nullopt);
            if (result.root_x.size() != 4)
                fail(name + ": no root node was traced");
            auto got = lower ? result.root_x[3].first : result.root_x[3].second;
            if (got != expected)
                fail(name + ": the tall rectangle's " + (lower ? "lower" : "upper") + " bound is " + to_string(got.raw_value) + ", expected " +
                    to_string(expected.raw_value));
            if (proofs && count_markers(name, "disjunctive2d cumulative relaxation time-table edge-finding") < 1)
                fail(name + ": no TTEF marker, so something else made the push");
            if (proofs && ! verify(name))
                fail(name + ": veripb rejected the TTEF certificate");
            if (! result.satisfiable)
                fail(name + ": the fixture is satisfiable, but no solution was found");
            auto control = probe(inst, ttef_off, nullopt);
            auto control_bound = lower ? control.root_x[3].first : control.root_x[3].second;
            if (control_bound == expected)
                fail(name + ": the bound moved with TTEF off, so the fixture says nothing about the profile");
        };
        // TTEF takes it to 3 over [0, 4), and then to 4 over [3, 4) with
        // nothing contained --- the profile alone, which is time-tabling as a
        // case of TTEF. 4 is tight: the tall one fits at 4 and not at 3.
        check_push(ttef_lb, "disjunctive_2d_relaxation_ttef_lb", true, 4_i);
        check_push(ttef_ub, "disjunctive_2d_relaxation_ttef_ub", false, 2_i);

        {
            auto markers =
                enumerate_and_check(ttef_lb, ttef_on, proofs ? make_optional(string{"disjunctive_2d_relaxation_ttef_enumerate"}) : nullopt);
            if (proofs && markers == 0)
                fail("ttef_enumerate: the rule never fired");
        }
    }

    // --- a time axis as wide as the bounded range (#1083) ----------------
    //
    // Only the resource axis is gated by width, so a rectangle free across the
    // whole bounded range in x puts windows into the energetic rungs' sweep
    // whose supply, H * (b - a), is past the end of Integer. That threw, with
    // proofs off as well. Each fixture here is one from above with such
    // rectangles added, and has to come out as the fixture did, with proofs
    // off and on: the wide windows are left alone, and the narrow ones still
    // fire.
    if (! overload && ! edge_finding && ! ttef && ! projection) {
        const Disjunctive2DRules overload_on{.relaxation_overload = true};
        const Disjunctive2DRules ef_on{.relaxation_edge_finding = true};
        const Disjunctive2DRules ttef_on{.relaxation_time_table_edge_finding = true};
        const Disjunctive2DRules all_on{
            .cumulative_relaxation = true, .relaxation_overload = true, .relaxation_edge_finding = true, .relaxation_time_table_edge_finding = true};
        auto with_wide = [](Instance inst, int y_hi) {
            inst.wide_y_ranges.emplace_back(0, y_hi);
            return inst;
        };
        auto names = [&](const string & name) {
            vector<optional<string>> result{nullopt};
            if (proofs)
                result.emplace_back(name);
            return result;
        };

        // The issue's instance: three unit squares, free in x, in a y window of
        // four. Nothing overloads anything, so every rule has a solution to
        // find.
        {
            Instance free_squares{};
            for (auto k = 0; k < 3; ++k)
                free_squares.wide_y_ranges.emplace_back(0, 3);
            for (const auto & [rules, rule] :
                {pair{overload_on, "overload"}, pair{ef_on, "edge_finding"}, pair{ttef_on, "ttef"}, pair{all_on, "all"}})
                for (const auto & name : names(string{"disjunctive_2d_relaxation_wide_free_"} + rule)) {
                    auto result = probe(free_squares, rules, name);
                    if (! result.satisfiable)
                        fail(string{"wide_free_"} + rule + ": three unit squares fit in any x, but no solution was found");
                    if (name && ! verify(*name))
                        fail(string{"wide_free_"} + rule + ": veripb rejected the proof");
                }
        }

        // The overload fixture, with a unit square free in x alongside: the
        // window [0, 5) still holds 28 units of area in 25.
        for (const auto & name : names("disjunctive_2d_relaxation_wide_overload_area")) {
            auto result = probe(with_wide(area, 4), overload_on, name);
            if (! result.refuted_at_root)
                fail("wide_overload_area: the root did not close, so a wide window stopped the sweep before the narrow one");
            if (name && count_markers(*name, "disjunctive2d cumulative relaxation overload") < 1)
                fail("wide_overload_area: no overload marker, so something else closed the root");
            if (name && ! verify(*name))
                fail("wide_overload_area: veripb rejected the certificate");
        }

        // The push fixtures, likewise: the pushed rectangle is the fourth, and
        // the wide square, fifth, is in no window the push comes from.
        auto check_push = [&](const Instance & inst, Disjunctive2DRules rules, const string & stem, const string & marker, Integer expected) {
            for (const auto & name : names(stem)) {
                auto result = probe(with_wide(inst, 3), rules, name);
                if (result.root_x.size() != 5)
                    fail(stem + ": no root node was traced");
                if (result.root_x[3].first != expected)
                    fail(stem + ": the tall rectangle's lower bound is " + to_string(result.root_x[3].first.raw_value) + ", expected " +
                        to_string(expected.raw_value));
                if (! result.satisfiable)
                    fail(stem + ": the fixture is satisfiable, but no solution was found");
                if (name && count_markers(*name, marker) < 1)
                    fail(stem + ": no marker, so something else made the push");
                if (name && ! verify(*name))
                    fail(stem + ": veripb rejected the proof");
            }
        };
        check_push(ef_lb, ef_on, "disjunctive_2d_relaxation_wide_edge_finding_lb", "disjunctive2d cumulative relaxation edge-finding", 3_i);
        check_push(ttef_lb, ttef_on, "disjunctive_2d_relaxation_wide_ttef_lb", "disjunctive2d cumulative relaxation time-table edge-finding", 4_i);
    }

    // --- Cumulative's own propagator on each projection (#973) -----------
    //
    // Disjunctive2DRules::cumulative_projection, which reaches the same
    // capacity rows as the rungs above but runs Cumulative's rules over them
    // rather than rules of this constraint's own. So the fixtures are the
    // rungs' own, and what they check is that the projection gets there too.
    if (! overload && ! edge_finding && ! ttef && ! projection) {
        auto only = [](auto set) {
            CumulativeRules rules{.time_table = false, .overload = false, .profile_overload = false};
            set(rules);
            return Disjunctive2DRules{.cumulative_projection = rules};
        };
        const auto tt_only = only([](CumulativeRules & r) { r.time_table = true; });
        const auto overload_only = only([](CumulativeRules & r) { r.overload = true; });
        // Cumulative's edge-finding runs inside its overload check's window
        // sweep, so it needs that on, and its TTEF is a strengthening of its
        // edge-finding, so that needs edge-finding on too. Each fixture's
        // control is the rule set one step down.
        const auto tt_and_overload = only([](CumulativeRules & r) {
            r.time_table = true;
            r.overload = true;
        });
        const auto ef_only = only([](CumulativeRules & r) {
            r.time_table = true;
            r.overload = true;
            r.edge_finding = true;
        });
        const auto ttef_only = only([](CumulativeRules & r) {
            r.time_table = true;
            r.overload = true;
            r.edge_finding = true;
            r.time_table_edge_finding = true;
        });
        const Disjunctive2DRules projection_all{.cumulative_projection = every_cumulative_rule};

        auto closes = [&](const Instance & inst, Disjunctive2DRules rules, const string & name) {
            auto result = probe(inst, rules, proofs ? make_optional(name) : nullopt);
            if (! result.refuted_at_root)
                fail(name + ": the root did not close");
            if (proofs && result.markers < 1)
                fail(name + ": no projection row was derived, so something else closed the root");
            if (proofs && ! verify(name))
                fail(name + ": veripb rejected the proof");
        };

        // Time-tabling alone refutes `sharp`, which the pairwise rule cannot.
        closes(sharp, tt_only, "disjunctive_2d_projection_sharp");

        // The overload check refutes `area`, and time-tabling cannot: no
        // square has a mandatory part.
        closes(area, overload_only, "disjunctive_2d_projection_area");
        if (probe(area, tt_only, nullopt, true).refuted_at_root)
            fail("projection_area: time-tabling closed the root too, so the fixture says nothing about the overload check");

        // Only the y projection overloads, which is what says the second axis
        // is keyed and wired up right: its flags are at positions n + i. The
        // rungs' `y_only` a unit higher, since Cumulative's overload check
        // leaves out a task whose start is a {0, 1} variable.
        {
            auto name = string{"disjunctive_2d_projection_y_only"};
            const Instance y_only{vector<pair<int, int>>(5, {0, 3}), {{1, 2}, {1, 2}, {1, 2}, {1, 2}, {4, 5}}, vector<int>(5, 2), vector<int>(5, 2)};
            closes(y_only, overload_only, name);
            if (proofs && count_markers(name, "disjunctive2d cumulative projection row axis=1") < 1)
                fail(name + ": no y-axis row was derived");
        }

        // The rungs' push fixtures, reached by Cumulative's rules of the same
        // names.
        auto check_push = [&](const Instance & inst, Disjunctive2DRules rules, Disjunctive2DRules control_rules, const string & name, bool lower,
                              Integer expected) {
            auto result = probe(inst, rules, proofs ? make_optional(name) : nullopt);
            if (result.root_x.size() != 4)
                fail(name + ": no root node was traced");
            auto got = lower ? result.root_x[3].first : result.root_x[3].second;
            if (got != expected)
                fail(name + ": the tall rectangle's " + (lower ? "lower" : "upper") + " bound is " + to_string(got.raw_value) + ", expected " +
                    to_string(expected.raw_value));
            if (proofs && ! verify(name))
                fail(name + ": veripb rejected the proof");
            if (! result.satisfiable)
                fail(name + ": the fixture is satisfiable, but no solution was found");
            auto control = probe(inst, control_rules, nullopt);
            if ((lower ? control.root_x[3].first : control.root_x[3].second) == expected)
                fail(name + ": the control made the same push, so the fixture says nothing about the rule");
        };
        check_push(ef_lb, ef_only, tt_and_overload, "disjunctive_2d_projection_ef_lb", true, 3_i);
        check_push(ef_ub, ef_only, tt_and_overload, "disjunctive_2d_projection_ef_ub", false, 3_i);
        check_push(ttef_lb, ttef_only, ef_only, "disjunctive_2d_projection_ttef_lb", true, 4_i);
        check_push(ttef_ub, ttef_only, ef_only, "disjunctive_2d_projection_ttef_ub", false, 2_i);

        // Soundness by enumeration against brute force, every rule on.
        const Instance tiling{vector<pair<int, int>>(4, {0, 2}), vector<pair<int, int>>(4, {0, 2}), vector<int>(4, 2), vector<int>(4, 2)};
        for (const auto & [inst, name] : {pair{tiling, "tiling"}, pair{ef_lb, "ef_lb"}, pair{ttef_lb, "ttef_lb"}}) {
            auto markers =
                enumerate_and_check(inst, projection_all, proofs ? make_optional("disjunctive_2d_projection_enumerate_" + string{name}) : nullopt);
            if (proofs && markers == 0)
                fail(string{"projection_enumerate_"} + name + ": no projection row was derived");
        }
    }

    // --- the flagged row's arithmetic, settled from the model (#1082) -----
    //
    // The row's network has constants quadratic in the resource-axis window,
    // so a window from zero overflows Integer once it ends at 2^31. The rules
    // citing the row are then off on that axis, proofs or not; before, they
    // fired with proofs off and threw part-way through the solve with them on.
    //
    // Three rectangles of height h in the column x = 0, each at y = lo or lo +
    // h: two stack, and three overload the column. The holes keep the search
    // small once the rule is off. A fourth, unit square at (2, lo) widens the
    // x extent to three, which keeps the y projection from firing (area 3h + 1
    // in 6h); that matters because its proof would name a row per time point
    // across a y axis this wide.
    if (! overload && ! edge_finding && ! ttef && ! projection) {
        const Disjunctive2DRules overload_on{.relaxation_overload = true};
        const Disjunctive2DRules projection_on{.cumulative_projection = CumulativeRules{}};

        struct Column
        {
            bool satisfiable = false;
            int x_rows = 0;
        };
        auto column = [&](Integer lo, Integer h, Disjunctive2DRules rules, const optional<string> & name) -> Column {
            Problem p;
            vector<IntegerVariableID> xs, ys;
            for (auto i = 0; i < 3; ++i) {
                xs.push_back(p.create_integer_variable(0_i, 0_i));
                ys.push_back(p.create_integer_variable(vector<Integer>{lo, lo + h}));
            }
            xs.push_back(p.create_integer_variable(2_i, 2_i));
            ys.push_back(p.create_integer_variable(lo, lo));
            p.post(Disjunctive2D{xs, ys, vector<Integer>(4, 1_i), vector<Integer>{h, h, h, 1_i}}.with_rules(rules));
            Column result;
            solve_with(p, SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                result.satisfiable = true;
                return false;
            }},
                name ? make_optional<ProofOptions>(ProofFileNames{*name}) : nullopt);
            if (name)
                result.x_rows = count_markers(*name, "disjunctive2d cumulative relaxation overload axis=0") +
                    count_markers(*name, "disjunctive2d cumulative projection row axis=0");
            return result;
        };

        auto check = [&](const string & name, Integer lo, Integer h, Disjunctive2DRules rules, bool row_expected) {
            if (column(lo, h, rules, nullopt).satisfiable)
                fail(name + ": three rectangles of height h fit in a column 2h tall, with proofs off");
            if (! proofs)
                return;
            auto result = column(lo, h, rules, name);
            if (result.satisfiable)
                fail(name + ": three rectangles of height h fit in a column 2h tall, with proofs on");
            if (row_expected && result.x_rows < 1)
                fail(name + ": no row on the x projection, so the fixture does not reach the network");
            if (! row_expected && result.x_rows != 0)
                fail(name + ": a row on the x projection, over a window its network cannot write");
            if (! verify(name))
                fail(name + ": veripb rejected the proof");
        };

        // A window from zero ending at 2^31 - 2: 31 bits, the widest that fits,
        // with `(1 + K) * span` just under 2^62.
        check("disjunctive_2d_relaxation_row_fits", 0_i, Integer{(1LL << 30) - 1}, overload_on, true);
        // Ending at 2^31: 32 bits, and `(1 + K) * span` is past 2^63.
        check("disjunctive_2d_relaxation_row_too_wide", 0_i, Integer{1LL << 30}, overload_on, false);
        // It is the window that decides, not the width: four units high up
        // the axis make a 39-bit network whose constants are small.
        check("disjunctive_2d_relaxation_row_high_narrow", Integer{1LL << 38}, 2_i, overload_on, true);

        // The projection cites the same row, and is gated with it, but only
        // the narrow window can be a fixture: the y axis is the others' wide
        // window, and the projection's Cumulative on it works per time point
        // across its horizon, proofs or not.
        check("disjunctive_2d_projection_row_high_narrow", Integer{1LL << 38}, 2_i, projection_on, true);
    }

    // --- a cap on the window's span (#1098) ------------------------------
    //
    // The energetic rungs' certificates cost a row per time point of the
    // window they cite, and Disjunctive2DRules::relaxation_max_span declines a
    // window wider than it, proofs or not. The cap is on the span, so each
    // rung's own fixture fires with the cap at its window's span and does not
    // one below it; and then #1082's column without its fourth square, which
    // the y projection refutes over a window 2^31 wide, is refuted by search
    // instead, with a proof small enough to write.
    if (! overload && ! edge_finding && ! ttef && ! projection) {
        auto capped = [](Disjunctive2DRules rules, Integer span) {
            rules.relaxation_max_span = span;
            return rules;
        };
        const Disjunctive2DRules overload_on{.relaxation_overload = true};
        const Disjunctive2DRules ef_on{.relaxation_edge_finding = true};
        const Disjunctive2DRules ttef_on{.relaxation_time_table_edge_finding = true};
        auto names = [&](const string & name) {
            vector<optional<string>> result{nullopt};
            if (proofs)
                result.emplace_back(name);
            return result;
        };

        // The widest window a rule's firings name in their markers, which is
        // what a cap has to bound: the rule can still fire under it, once
        // search has narrowed some window below it.
        auto widest_firing = [](const string & basename, const string & marker) -> Integer {
            ifstream f{basename + ".pbp"};
            string line;
            auto widest = 0_i;
            while (getline(f, line)) {
                auto at = line.find("window=[");
                if (line.find(marker) == string::npos || at == string::npos)
                    continue;
                auto comma = line.find(',', at), close = line.find(')', at);
                auto a = std::stoll(line.substr(at + 8, comma - at - 8)), b = std::stoll(line.substr(comma + 1, close - comma - 1));
                widest = std::max(widest, Integer{b - a});
            }
            return widest;
        };

        // `area`'s one window is [0, 5). Declined, the root stays open and
        // search has 101,221 nodes to go, so this side is root-only.
        for (const auto & name : names("disjunctive_2d_relaxation_span_cap_overload")) {
            auto result = probe(area, capped(overload_on, 5_i), name);
            if (! result.refuted_at_root)
                fail("span_cap_overload: a cap of the window's own span stopped the overload");
            if (name && ! verify(*name))
                fail("span_cap_overload: veripb rejected the certificate");
        }
        if (probe(area, capped(overload_on, 4_i), nullopt, true).refuted_at_root)
            fail("span_cap_overload: a cap one below the window's span did not stop the overload");

        // The pushes come from [0, 4), and are satisfiable, so both sides
        // can run to a solution with proofs on.
        auto check_push = [&](const Instance & inst, Disjunctive2DRules rules, const string & stem, const string & marker, Integer expected) {
            auto control = probe(inst, Disjunctive2DRules{}, nullopt, true);
            if (control.root_x.size() != 4 || control.root_x[3].first == expected)
                fail(stem + ": the push is made without the rule, so the fixture cannot show the cap");
            for (auto span : {4_i, 3_i})
                for (const auto & name : names(stem + "_" + to_string(span.raw_value))) {
                    auto result = probe(inst, capped(rules, span), name);
                    auto want = span == 4_i ? expected : control.root_x[3].first;
                    if (result.root_x.size() != 4)
                        fail(stem + ": no root node was traced");
                    if (result.root_x[3].first != want)
                        fail(stem + ": under a cap of " + to_string(span.raw_value) + " the tall rectangle's lower bound is " +
                            to_string(result.root_x[3].first.raw_value) + ", expected " + to_string(want.raw_value));
                    if (! result.satisfiable)
                        fail(stem + ": the fixture is satisfiable, but no solution was found");
                    if (name && widest_firing(*name, marker) > span)
                        fail(stem + ": the rule fired on a window wider than the cap of " + to_string(span.raw_value));
                    if (name && span == 4_i && widest_firing(*name, marker) != span)
                        fail(stem + ": the rule did not fire on the window the push comes from");
                    if (name && ! verify(*name))
                        fail(stem + ": veripb rejected the proof");
                }
        };
        check_push(ef_lb, ef_on, "disjunctive_2d_relaxation_span_cap_edge_finding", "disjunctive2d cumulative relaxation edge-finding", 3_i);
        check_push(ttef_lb, ttef_on, "disjunctive_2d_relaxation_span_cap_ttef", "disjunctive2d cumulative relaxation time-table edge-finding", 4_i);

        // The wide column. The holes keep the search to eight leaves.
        struct Column
        {
            bool refuted_at_root = false, satisfiable = false;
        };
        auto column = [&](Disjunctive2DRules rules, const optional<string> & name) -> Column {
            Problem p;
            auto h = Integer{1LL << 30};
            vector<IntegerVariableID> xs, ys;
            for (auto i = 0; i < 3; ++i) {
                xs.push_back(p.create_integer_variable(0_i, 0_i));
                ys.push_back(p.create_integer_variable(vector<Integer>{0_i, h}));
            }
            p.post(Disjunctive2D{xs, ys, vector<Integer>(3, 1_i), vector<Integer>(3, h)}.with_rules(rules));
            Column result;
            auto reached_a_node = false;
            solve_with(p,
                SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                                   result.satisfiable = true;
                                   return false;
                               },
                    .trace = [&](const CurrentState &) -> bool {
                        reached_a_node = true;
                        return true;
                    }},
                name ? make_optional<ProofOptions>(ProofFileNames{*name}) : nullopt);
            result.refuted_at_root = ! reached_a_node && ! result.satisfiable;
            return result;
        };

        // Uncapped, and only with proofs off: this is the proof #1098 could not
        // write.
        if (! column(overload_on, nullopt).refuted_at_root)
            fail("span_cap_column: the uncapped overload did not refute the root, so the fixture does not reach the wide window");
        for (const auto & name : names("disjunctive_2d_relaxation_span_cap_column")) {
            auto result = column(capped(overload_on, Integer{1LL << 16}), name);
            if (result.refuted_at_root)
                fail("span_cap_column: the root was refuted under the cap");
            if (result.satisfiable)
                fail("span_cap_column: three rectangles of height h fit in a column 2h tall");
            if (name && widest_firing(*name, "disjunctive2d cumulative relaxation overload") > Integer{1LL << 16})
                fail("span_cap_column: an overload fired on a window wider than the cap");
            if (name && ! verify(*name))
                fail("span_cap_column: veripb rejected the proof");
        }
    }

    println(cerr, "disjunctive2d cumulative relaxation: all fixtures pass");
    return EXIT_SUCCESS;
}
