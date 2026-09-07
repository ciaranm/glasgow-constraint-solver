#include <gcs/constraints/equals.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/current_state.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <gcs/stats.hh>

#include <cstdlib>
#include <fstream>
#include <functional>
#include <iostream>
#include <random>
#include <set>
#include <string>
#include <tuple>
#include <type_traits>
#include <utility>
#include <vector>

using std::cerr;
using std::flush;
using std::function;
using std::is_same_v;
using std::make_optional;
using std::mt19937;
using std::nullopt;
using std::pair;
using std::set;
using std::string;
using std::tuple;
using std::variant;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
using fmt::println;
#endif

using namespace gcs;
using namespace gcs::test_innards;

template <typename Constraint_>
auto run_equals_test(const string & which, bool proofs, const ViewWrapConfig & view_cfg, variant<int, pair<int, int>> v1_range,
    variant<int, pair<int, int>> v2_range, const function<auto(int, int, int)->bool> & is_satisfying) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 2);
    visit([&](auto v1,
              auto v2) { print(cerr, "equals {} [{}] {} {} {}", which, view_wrap_config_label(view_cfg), v1, v2, proofs ? " with proofs:" : ":"); },
        v1_range, v2_range);
    cerr << flush;

    pair<int, int> v3_range{0, 1};
    set<tuple<int, int, int>> expected, actual;
    build_expected(expected, is_satisfying, v1_range, v2_range, v3_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = visit([&](auto b) { return create_integer_variable_or_constant_with_view(p, b, wraps.at(0)); }, v1_range);
    auto v2 = visit([&](auto b) { return create_integer_variable_or_constant_with_view(p, b, wraps.at(1)); }, v2_range);
    auto v3 = p.create_integer_variable(0_i, 1_i);
    if constexpr (is_same_v<Constraint_, Equals>) {
        p.post(Constraint_{v1, v2});
    }
    else if constexpr (is_same_v<Constraint_, NotEquals>) {
        p.post(Constraint_{v1, v2});
    }
    else {
        p.post(Constraint_{v1, v2, v3 == 1_i});
    }

    auto proof_name = proofs ? make_optional("equals_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2, v3});

    check_results(proof_name, expected, actual);
}

// Dup-variable test: post a constraint with the same handle in both
// variable slots. Consistency is intentionally not checked: a GAC
// algorithm for distinct variables doesn't generally yield GAC under
// aliasing, and fixing it varies in difficulty per constraint. We
// verify the solution set and the proof only.
template <typename Constraint_>
auto run_dup_equals_test(const string & filename_tag, bool proofs, pair<int, int> x_range, const function<auto(int, int)->bool> & is_satisfying)
    -> void
{
    print(cerr, "equals dup {} {} {}", filename_tag, x_range, proofs ? " with proofs:" : ":");
    cerr << flush;

    pair<int, int> c_range{0, 1};
    set<tuple<int, int>> expected, actual;
    build_expected(expected, is_satisfying, x_range, c_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto x = p.create_integer_variable(Integer(x_range.first), Integer(x_range.second));
    auto c = p.create_integer_variable(0_i, 1_i);
    if constexpr (is_same_v<Constraint_, Equals> || is_same_v<Constraint_, NotEquals>) {
        p.post(Constraint_{x, x});
    }
    else {
        p.post(Constraint_{x, x, c == 1_i});
    }

    auto proof_name = proofs ? make_optional("equals_test_dup_" + filename_tag) : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{x, c});

    check_results(proof_name, expected, actual);
}

auto run_no_overlap_equals_test(bool proofs) -> void
{
    print(cerr, "no overlap equals {}", proofs ? " with proofs:" : ":");
    cerr << flush;

    pair<int, int> x_range{1, 10};
    pair<int, int> y_range{1, 10};
    pair<int, int> z_range{0, 1};
    pair<int, int> c_range{0, 1};
    set<tuple<int, int, int, int>> expected, actual;
    build_expected(
        expected,
        [](int x, int y, int z, int c) -> bool {
            if (x == 4 && c != 0)
                return false;
            if (x == 5 && c != 0)
                return false;
            if (x == 6 && c != 0)
                return false;
            if (x == 9 && c != 0)
                return false;
            if (x == 10 && c != 0)
                return false;

            if (y == 1 && c != 0)
                return false;
            if (y == 2 && c != 0)
                return false;
            if (y == 3 && c != 0)
                return false;
            if (y == 6 && c != 0)
                return false;
            if (y == 7 && c != 0)
                return false;
            if (y == 8 && c != 0)
                return false;

            if (z == 1) {
                if (x != y)
                    return false;
            }
            return true;
        },
        x_range, y_range, z_range, c_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto x = p.create_integer_variable(1_i, 10_i);
    auto y = p.create_integer_variable(1_i, 10_i);
    auto z = p.create_integer_variable(0_i, 1_i);
    auto c = p.create_integer_variable(0_i, 1_i);
    p.post(EqualsIf{x, y, z == 1_i});

    p.post(EqualsIf{c, 0_c, x == 4_i});
    p.post(EqualsIf{c, 0_c, x == 5_i});
    p.post(EqualsIf{c, 0_c, x == 6_i});
    p.post(EqualsIf{c, 0_c, x == 9_i});
    p.post(EqualsIf{c, 0_c, x == 10_i});

    p.post(EqualsIf{c, 0_c, y == 1_i});
    p.post(EqualsIf{c, 0_c, y == 2_i});
    p.post(EqualsIf{c, 0_c, y == 3_i});
    p.post(EqualsIf{c, 0_c, y == 6_i});
    p.post(EqualsIf{c, 0_c, y == 7_i});
    p.post(EqualsIf{c, 0_c, y == 8_i});

    auto proof_name = proofs ? make_optional("equals_test") : nullopt;
    // x, y, z are each GAC (a single EqualsIf is GAC, and c=1 does propagate
    // x != 4 etc. via the contrapositive). But c is only network-GAC: c=1 is
    // unsupported at z=1 because x==y combined with *all* the c -> x not in {...}
    // / c -> y not in {...} implications leaves no common value -- a deduction
    // across all 13 posted constraints that no individual EqualsIf propagator
    // can make (GAC of a conjunction != conjunction of GAC). So c is None.
    solve_for_tests_checking_consistency(p, proof_name, expected, actual,
        tuple{pair{x, CheckConsistency::GAC}, pair{y, CheckConsistency::GAC}, pair{z, CheckConsistency::GAC}, pair{c, CheckConsistency::None}});

    check_results(proof_name, expected, actual);
}

// The nmseq shape in miniature: an indicator b[v] per value, each posted as a
// reified equality between x and the *constant* v, plus a driver g[v] that
// punches v out of x's interior on its own.
//
// The driver is what makes this lane different from every other one here. Every
// other test posts a single constraint over its operands, so nothing ever
// removes an interior value from one: the only domain event a propagator is
// asked about is an instantiation, and a trigger that can see nothing finer
// passes. Nor is it enough to punch the hole with a disequality against another
// branched variable -- tried, and the search fixed b[v] before it ever got round
// to making the hole, so the interesting node was never reached. g[v] = 1 makes
// the hole directly, from a variable the brancher can reach while b[v] is still
// free, and then b[v] = 0 is a pruning nothing else in the model can make.
//
// A trigger that misses it loses no solutions -- search still finds the right
// answer, just after exploring a subtree it should have pruned -- so this is
// checked as consistency at every node, not as a solution set. It is what stands
// behind the constant-operand triggers in ReifiedEquals::install_propagators;
// dropping the refined watch and leaving only on_instantiated fails it. Note
// that g[v]'s own constraint has a constant operand too, so the not-equals-if
// arm of the same reasoning is under test alongside the equals-iff one. See
// issue #889.
auto run_value_indicator_equals_test(bool proofs, int n) -> void
{
    print(cerr, "value indicator equals {}{}", n, proofs ? " with proofs:" : ":");
    cerr << flush;

    // x takes some value; b says which; g[v] may forbid v, and may not forbid
    // the value x actually takes.
    set<tuple<int, vector<int>, vector<int>>> expected, actual;
    for (int xv = 0; xv < n; ++xv) {
        vector<int> bs;
        for (int v = 0; v < n; ++v)
            bs.push_back(xv == v ? 1 : 0);
        for (int mask = 0; mask < (1 << n); ++mask) {
            if (mask & (1 << xv))
                continue;
            vector<int> gs;
            for (int v = 0; v < n; ++v)
                gs.push_back((mask >> v) & 1);
            expected.emplace(xv, bs, gs);
        }
    }
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto x = p.create_integer_variable(0_i, Integer{n - 1});
    vector<IntegerVariableID> bs, gs;
    for (int v = 0; v < n; ++v) {
        bs.push_back(p.create_integer_variable(0_i, 1_i));
        gs.push_back(p.create_integer_variable(0_i, 1_i));
    }

    for (int v = 0; v < n; ++v) {
        p.post(EqualsIff{x, constant_variable(Integer{v}), bs[v] == 1_i});
        p.post(NotEqualsIf{x, constant_variable(Integer{v}), gs[v] == 1_i});
    }

    // Every position is GAC, and each is achieved by a single propagator over
    // its own scope: b[v] = 1 dies exactly when v leaves x, g[v] = 1 dies
    // exactly when x is fixed at v, and x loses v exactly when b[v] = 0 or
    // g[v] = 1. No deduction here crosses two constraints.
    auto proof_name = proofs ? make_optional("equals_test_value_indicator_" + std::to_string(n)) : nullopt;
    solve_for_tests_checking_consistency(
        p, proof_name, expected, actual, tuple{pair{x, CheckConsistency::GAC}, pair{bs, CheckConsistency::GAC}, pair{gs, CheckConsistency::GAC}});

    check_results(proof_name, expected, actual);
}

// A reified equals whose operands are disjoint but *interleaved*: each one's
// values sit in the other's holes, so no bound separates them and the witness
// has to account for every run. This is the shape the interval certificate of
// #867 exists for, and the only one in this file that reaches the two moves
// that carry a range literal -- "v1 has nothing in [lo, hi]", which needs no
// lemma, and "v2 has nothing in [lo, hi]", which needs two.
//
// Both orders are run, because the walk is not symmetric: it climbs v1's domain,
// so which operand is first decides whether it starts at v1's lower bound or at
// v2's, and whether it ends by running off the top of v1 or of v2. Between them
// the two orders reach all six moves.
//
// Proofs on, and it is the proof that is the point: the reason is stated over
// intervals, and the conclusion is only RUP if the lemmas emitted alongside it
// let unit propagation see those interval literals through. Verified, so a
// missing lemma is a red lane rather than a silently weaker proof.
auto run_holey_no_overlap_equals_test(bool proofs, bool swapped) -> void
{
    print(cerr, "holey no overlap equals {}{}", swapped ? "swapped" : "plain", proofs ? " with proofs:" : ":");
    cerr << flush;

    // Two blocks each, interleaved: {0..3, 8..11} against {4..7, 12..15}.
    vector<Integer> lower_first, upper_first;
    for (Integer v = 0_i; v <= 15_i; ++v)
        ((v / 4_i) % 2_i == 0_i ? lower_first : upper_first).push_back(v);

    set<tuple<int, int, int>> expected, actual;
    for (const auto & xv : swapped ? upper_first : lower_first)
        for (const auto & yv : swapped ? lower_first : upper_first)
            expected.emplace(static_cast<int>(xv.raw_value), static_cast<int>(yv.raw_value), 0);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto x = p.create_integer_variable(swapped ? upper_first : lower_first);
    auto y = p.create_integer_variable(swapped ? lower_first : upper_first);
    auto b = p.create_integer_variable(0_i, 1_i);
    p.post(EqualsIff{x, y, b == 1_i});

    auto proof_name = proofs ? make_optional("equals_test_holey_" + string{swapped ? "swapped" : "plain"}) : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{x, y, b});

    check_results(proof_name, expected, actual);
}

// A reified equals whose operands are wide and do not overlap. Nothing else in
// this file goes anywhere near this shape: every other domain here lives inside
// [-10, 10], and range_infer_test works inside [0, 40], so the no-overlap rule
// had never been asked a question whose answer depends on the width at all.
//
// What this pins is the *answer*: root propagation alone must decide the
// condition, at a width where deciding it by looking at values cannot work.
// Note what it does not pin. It would have passed before #864 was fixed too --
// the unguarded reason walk gave the same answer, having spent 78 GB and 160 s
// to do it, with proofs off. Cost is not checkable from here; the ReifiedEquals
// row of the large-domain audit lane is what holds that down, and it has the
// guard instrumentation to fail rather than merely take a long time.
//
// Proofs off only, and deliberately: at this width the *reason* is the thing
// under test and it is only built when reasons are wanted. The proof side has
// its own test below, at a width whose regression is slow rather than fatal.
//
// Solutions are not enumerated: there are ~2.5e17 of them. Search stops at the
// first node, which is reached only once root propagation has finished.
auto run_wide_no_overlap_equals_test() -> void
{
    const auto width = 1000000000_i;
    println(cerr, "wide no overlap equals: expecting the condition to be false after root propagation");

    Problem p;
    auto x = p.create_integer_variable(0_i, width / 2_i);
    auto y = p.create_integer_variable(width / 2_i + 1_i, width);
    auto b = p.create_integer_variable(0_i, 1_i);
    p.post(EqualsIff{x, y, b == 1_i});

    bool reached_a_node = false, condition_is_false = false;
    auto check = [&](const CurrentState & s) {
        reached_a_node = true;
        condition_is_false = s.has_single_value(b) && s(b) == 0_i;
        return false;
    };

    solve_with(p, SolveCallbacks{.solution = check, .trace = check, .stats_report = silent_stats_report()});

    if (! reached_a_node)
        throw UnexpectedException{"wide no overlap equals test never reached a node"};
    if (! condition_is_false)
        throw UnexpectedException{"wide no overlap equals did not force its condition false at the root"};
}

// The same shape, proved, and this one pins the *cost*: it fails if the witness
// goes back to being one line per value.
//
// Before #867 the rule's justification emitted one RUP line per value in the
// first operand's bounds range, so a proving run at this width wrote a hundred
// megabytes of proof for a fact that two bounds settle -- which is why the test
// above could only be run with proofs off. The interval witness states it in a
// fixed handful of lines at any width, so the assertion is on the proof's line
// count, checked before the proof is handed to veripb.
//
// The bound is loose, and deliberately not a pinned figure. Most of what a proof
// this small contains is fixed overhead -- the header, the initial bound axioms,
// the order-encoding definitions the conclusion's literals pull in -- and that
// part is free to move as unrelated proof scaffolding changes, whereas the thing
// under test is whether the witness is a constant or a million lines. Any
// threshold between the two separates them; pinning the exact figure would only
// buy a lane that goes red for reasons that have nothing to do with this rule.
//
// The width is 10^6 rather than the 10^9 above: a regression must fail, not
// wedge, and at 10^9 a per-value witness would fill the disk before anything
// could notice.
auto run_wide_proved_no_overlap_equals_test() -> void
{
    const auto width = 1000000_i;
    const auto line_budget = 1000;
    println(cerr, "wide no overlap equals with proofs: expecting a proof of well under {} lines", line_budget);

    Problem p;
    auto x = p.create_integer_variable(0_i, width / 2_i);
    auto y = p.create_integer_variable(width / 2_i + 1_i, width);
    auto b = p.create_integer_variable(0_i, 1_i);
    p.post(EqualsIff{x, y, b == 1_i});

    // Solutions are not enumerated: there are ~2.5e11 of them. Stopping at the
    // first node still completes a checkable proof, exactly as
    // check_initialisation_only_for_tests does.
    const string proof_name = "equals_test_wide_proved";
    solve_with(
        p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return false; }}, make_optional<ProofOptions>(ProofFileNames{proof_name}));

    auto lines = 0;
    {
        std::ifstream proof{proof_name + ".pbp"};
        if (! proof)
            throw UnexpectedException{"wide proved no overlap equals wrote no proof"};
        for (string line; getline(proof, line);)
            ++lines;
    }
    println(cerr, "wide no overlap equals proof is {} lines", lines);
    if (lines > line_budget)
        throw UnexpectedException{"wide proved no overlap equals wrote " + std::to_string(lines) +
            " proof lines, which is not a witness whose size is independent of the domain width"};

    verify_proof_and_clean_up(proof_name);
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);
    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    // Single-position config that names a position the constraint doesn't
    // have collapses to "all bare", which the baseline (no flags) already
    // covers. Skip with a success exit so ctest sees it as benign.
    constexpr int n_positions = 2;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "equals view sweep: position {} out of range for n_positions = {}; skipping", *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    vector<pair<variant<int, pair<int, int>>, variant<int, pair<int, int>>>> data = {
        {pair{2, 5}, pair{1, 6}},     //
        {pair{1, 6}, pair{2, 5}},     //
        {pair{1, 3}, pair{1, 3}},     //
        {pair{1, 5}, pair{6, 8}},     //
        {pair{1, 1}, pair{2, 4}},     //
        {pair{-2, -2}, pair{-2, -1}}, //
        {pair{1, 3}, pair{5, 8}},     //
        {pair{4, 13}, pair{3, 16}},   //
        {pair{-2, 4}, pair{-8, 7}},   //
        {pair{-7, 3}, pair{-10, 5}},  //
        // issue #254: genuine all-constant operands (ConstantIntegerVariableID),
        // both directions. Each Equals/NotEquals (and reified) mode is computed
        // from build_expected: 4==4 holds, 4==5 does not.
        {4, 4},  //
        {4, 5},  //
        {-3, -3} //
    };

    mt19937 rand(*get_seed());
    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_bounds(-10, 10, 5, 15), random_bounds(-10, 10, 5, 15));
    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_constant(-10, 10), random_bounds(-10, 10, 5, 15));
    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_bounds(-10, 10, 5, 15), random_constant(-10, 10));

    // no_overlap_equals_test fixes its own variable construction and isn't
    // currently part of the view sweep, so only run it for the baseline.
    bool run_no_overlap = view_wrap_config_is_effectively_bare(view_cfg, n_positions);

    // Bare-handle dup ranges. Skipped under the view-wrap sweep (which
    // mutates positional view-wraps in ways that aren't aliasing-aware).
    vector<pair<int, int>> dup_data = {
        {0, 0}, {0, 1}, {0, 5}, {-3, 3}, {2, 5} //
    };

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        if (run_no_overlap) {
            run_no_overlap_equals_test(proofs);
            run_value_indicator_equals_test(proofs, 4);
            run_value_indicator_equals_test(proofs, 6);
            run_holey_no_overlap_equals_test(proofs, false);
            run_holey_no_overlap_equals_test(proofs, true);
            if (proofs)
                run_wide_proved_no_overlap_equals_test();
            else
                run_wide_no_overlap_equals_test();
        }
        for (auto & [r1, r2] : data) {
            run_equals_test<Equals>("equals", proofs, view_cfg, r1, r2, [](int a, int b, int) { return a == b; });
            run_equals_test<EqualsIf>("equals if", proofs, view_cfg, r1, r2, [](int a, int b, int f) { return (! f) || (a == b); });
            run_equals_test<EqualsIff>("equals iff", proofs, view_cfg, r1, r2, [](int a, int b, int f) { return (a == b) == f; });
            run_equals_test<NotEquals>("not equals", proofs, view_cfg, r1, r2, [](int a, int b, int) { return a != b; });
            run_equals_test<NotEqualsIf>("not equals if", proofs, view_cfg, r1, r2, [](int a, int b, int f) { return (! f) || (a != b); });
            run_equals_test<NotEqualsIff>("not equals iff", proofs, view_cfg, r1, r2, [](int a, int b, int f) { return (a != b) == f; });
        }
        if (view_wrap_config_is_effectively_bare(view_cfg, n_positions))
            for (auto & x_range : dup_data) {
                run_dup_equals_test<Equals>("equals", proofs, x_range, [](int, int) { return true; });
                run_dup_equals_test<EqualsIf>("equals_if", proofs, x_range, [](int, int) { return true; });
                run_dup_equals_test<EqualsIff>("equals_iff", proofs, x_range, [](int, int c) { return c == 1; });
                run_dup_equals_test<NotEqualsIff>("notequals_iff", proofs, x_range, [](int, int c) { return c == 0; });
                // NotEqualsIf(x, x, c) ≡ c → x ≠ x ≡ ¬c. Was Bucket B
                // (propagator silent on alias) — fixed by alias check in
                // ReifiedEquals' infer_cond_when_undecided.
                run_dup_equals_test<NotEqualsIf>("notequals_if", proofs, x_range, [](int, int c) { return c == 0; });
            }
    }

    {
        // NotEquals on aliased operands is trivially unsat; reject at
        // construction rather than discovering after search.
        Problem p;
        auto x = p.create_integer_variable(Integer{0}, Integer{3});
        try {
            p.post(NotEquals{x, x});
            cerr << "expected NotEquals(x,x) to throw InvalidProblemDefinitionException" << '\n';
            return EXIT_FAILURE;
        }
        catch (const InvalidProblemDefinitionException &) {
        }
    }

    return EXIT_SUCCESS;
}
