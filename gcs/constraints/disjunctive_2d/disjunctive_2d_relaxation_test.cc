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
    };

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
        p.post(Disjunctive2D{xs, ys, widths, heights}.with_rules(rules).with_proof_mutation(mutation));
        return {xs, ys};
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
            result.markers = count_markers(*proof_name, "disjunctive2d cumulative relaxation ");
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

        auto markers = proof_name ? count_markers(*proof_name, "disjunctive2d cumulative relaxation ") : 0;
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
    auto run_random_sweep(int search_instances, bool proofs, Disjunctive2DRules with, Disjunctive2DRules without) -> void
    {
        mt19937 rand;
        rand.seed(1234);
        auto total_markers = 0;
        auto pruned_somewhere = false;
        for (auto instance = 0; instance < search_instances; ++instance) {
            auto n = uniform_int_distribution<int>{2, 4}(rand);
            Instance inst;
            for (auto i = 0; i < n; ++i) {
                inst.widths.push_back(uniform_int_distribution<int>{1, 3}(rand));
                inst.heights.push_back(uniform_int_distribution<int>{1, 3}(rand));
                inst.x_ranges.emplace_back(0, uniform_int_distribution<int>{0, 3}(rand));
                inst.y_ranges.emplace_back(0, uniform_int_distribution<int>{0, 3}(rand));
            }
            auto name = "disjunctive_2d_relaxation_search_" + to_string(instance);
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
    auto proofs = gcs::test_innards::can_run_veripb();
    auto search_instances = 0;
    optional<Disjunctive2DProofMutation> mutation;
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
        else if (arg == "--proof-files-basename" && a + 1 < argc)
            mutation_basename = argv[++a];
    }

    const Disjunctive2DRules with{.cumulative_relaxation = true};
    const Disjunctive2DRules without{.cumulative_relaxation = false};

    if (search_instances > 0) {
        run_random_sweep(search_instances, proofs, with, without);
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
    if (mutation) {
        Problem p;
        if (std::holds_alternative<disjunctive_2d_proof_mutation::SkipEscapePins>(*mutation))
            post_two_escapes(p, with, *mutation);
        else
            post(p, sharp, with, *mutation);
        solve_with(p, SolveCallbacks{}, make_optional<ProofOptions>(ProofFileNames{mutation_basename}));
        if (count_markers(mutation_basename, "disjunctive2d cumulative relaxation ") == 0)
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
        if (proofs && count_markers(name, "disjunctive2d cumulative relaxation ") < 1)
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
        if (proofs && count_markers(name, "disjunctive2d cumulative relaxation ") < 1)
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
        auto markers = proofs ? count_markers(name, "disjunctive2d cumulative relaxation ") : 0;
        gcs::test_innards::check_results(proofs ? make_optional(name) : nullopt, expected, actual);
        if (proofs && markers == 0)
            fail(name + ": the rule never fired, so this route through the certificate went unchecked");
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

    println(cerr, "disjunctive2d cumulative relaxation: all fixtures pass");
    return EXIT_SUCCESS;
}
