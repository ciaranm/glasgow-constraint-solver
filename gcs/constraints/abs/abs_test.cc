#include <gcs/constraints/abs.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <random>
#include <set>
#include <tuple>
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
using std::flush;
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

auto run_abs_test(bool proofs, const ViewWrapConfig & view_cfg, variant<int, pair<int, int>> v1_range, variant<int, pair<int, int>> v2_range) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 2);
    visit([&](auto v1, auto v2) { print(cerr, "abs [{}] {} {} {}", view_wrap_config_label(view_cfg), v1, v2, proofs ? " with proofs:" : ":"); },
        v1_range, v2_range);
    cerr << flush;

    auto is_satisfying = [](int a, int b) { return b == abs(a); };

    set<pair<int, int>> expected, actual;
    build_expected(expected, is_satisfying, v1_range, v2_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = visit([&](auto b) { return create_integer_variable_or_constant_with_view(p, b, wraps.at(0)); }, v1_range);
    auto v2 = visit([&](auto b) { return create_integer_variable_or_constant_with_view(p, b, wraps.at(1)); }, v2_range);
    p.post(Abs{v1, v2});

    auto proof_name = proofs ? make_optional("abs_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2});

    check_results(proof_name, expected, actual);
}

// Dup-variable test: Abs(x, x) forces x = abs(x), i.e. x >= 0.
// Consistency isn't checked on dup runs; see tmp/duplicate_var_audit.md.
auto run_dup_abs_test(bool proofs, pair<int, int> x_range) -> void
{
    print(cerr, "abs dup {} {}", x_range, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int>> expected, actual;
    build_expected(expected, [](int a) { return a == abs(a); }, x_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto x = p.create_integer_variable(Integer{x_range.first}, Integer{x_range.second});
    p.post(Abs{x, x});

    auto proof_name = proofs ? make_optional("abs_test_dup") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{x});

    check_results(proof_name, expected, actual);
}

// Interior hole pruning over sparse domains (issue #875). The interval removals
// live only on this path, and nothing in the data table can reach it: every row
// there is a contiguous range or a constant, and a contiguous domain has no
// interior hole to remove.
//
// The two loops need different shapes, which is why this takes both domains as
// value lists. The preimage loop wants a hole in v2, and the random rows above
// do reach that one. The *image* loop wants v1's image under abs to skip a run
// that v2 contains, which takes a hole in v1 -- and before this existed, no test
// in the suite reached it at all.
auto run_abs_hole_test(
    bool proofs, const ViewWrapConfig & view_cfg, const string & label, const vector<int> & v1_values, const vector<int> & v2_values) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 2);

    // Sizes and extremes rather than the lists: preimage_far's v1 is 101 values
    // wide and dumping it buries every other line of the run.
    print(cerr, "abs holes [{}] [{}] v1={} values in [{},{}] v2={} values in [{},{}]{}", label, view_wrap_config_label(view_cfg), v1_values.size(),
        v1_values.front(), v1_values.back(), v2_values.size(), v2_values.front(), v2_values.back(), proofs ? " with proofs:" : ":");
    cerr << flush;

    set<pair<int, int>> expected, actual;
    for (auto a : v1_values)
        for (auto b : v2_values)
            if (b == abs(a))
                expected.emplace(a, b);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = create_integer_variable_or_constant_with_view(p, v1_values, wraps.at(0));
    auto v2 = create_integer_variable_or_constant_with_view(p, v2_values, wraps.at(1));
    p.post(Abs{v1, v2});

    auto proof_name = proofs ? make_optional("abs_test_holes_" + label + "_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2});

    check_results(proof_name, expected, actual);
}

// Targeted tests for the proofs Abs::prepare emits for its four consequence
// bounds. Domains are picked so that one specific bound is non-trivial, so a
// proof failure points unambiguously at that bound. Uses
// check_initialisation_only_for_tests to verify just the initialisation proof
// (cheap: no full search, no solution enumeration).
auto run_abs_initialiser_test(const string & label, pair<int, int> v1_range, pair<int, int> v2_range) -> void
{
    print(cerr, "abs initialiser [{}] v1=[{},{}] v2=[{},{}] with proofs\n", label, v1_range.first, v1_range.second, v2_range.first, v2_range.second);
    cerr << flush;

    Problem p;
    auto v1 = p.create_integer_variable(Integer{v1_range.first}, Integer{v1_range.second});
    auto v2 = p.create_integer_variable(Integer{v2_range.first}, Integer{v2_range.second});
    p.post(Abs{v1, v2});

    check_initialisation_only_for_tests(p, "abs_initialiser_" + label);
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    constexpr int n_positions = 2;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "abs view sweep: position {} out of range for n_positions = {}; skipping", *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    // Initialiser tests use fixed labels and bounds keyed to specific
    // consequence-bound proofs; they're independent of the view sweep and
    // only run on the baseline.
    bool run_initialisers = view_wrap_config_is_effectively_bare(view_cfg, n_positions);

    vector<pair<variant<int, pair<int, int>>, variant<int, pair<int, int>>>> data = {{pair{2, 5}, pair{1, 6}}, //
        {pair{1, 6}, pair{2, 5}},                                                                              //
        {pair{1, 3}, pair{1, 3}},                                                                              //
        {pair{1, 5}, pair{6, 8}},                                                                              //
        {pair{1, 1}, pair{2, 4}},                                                                              //
        {pair{-5, 5}, pair{-5, 5}},                                                                            //
        {pair{-1, 6}, pair{-2, 5}},                                                                            //
        {pair{1, 3}, pair{-1, 3}},                                                                             //
        {pair{-1, 5}, pair{-6, 8}},                                                                            //
        {pair{-1, 1}, pair{-2, 4}},                                                                            //
        // Tight 0/1-style domains (issue #446): the consequence bounds land
        // exactly on declared domain boundaries, where the defining item for
        // the justification's atoms is a bare literal rather than a proof
        // line. These used to crash with bad_variant_access.
        {pair{0, 1}, pair{0, 1}},  //
        {pair{-1, 0}, pair{0, 1}}, //
        {pair{0, 2}, pair{0, 1}},  //
        {pair{0, 1}, pair{-1, 2}}, //
        {pair{-1, 1}, pair{0, 1}}, //
        {pair{-2, 0}, pair{0, 2}}, //
        // All-constant arguments (issue #254): both operands are
        // ConstantIntegerVariableIDs, so the constraint reduces to a
        // true/false check on abs(c1) == c2. Both directions are covered.
        {2, 2},  // abs(2) == 2: tautology
        {2, 3},  // abs(2) != 3: contradiction
        {-4, 4}, // abs(-4) == 4: tautology
        {-4, 5}, // abs(-4) != 5: contradiction
        {0, 0},  // abs(0) == 0: tautology
        {-7, 6}, // abs(-7) != 6: contradiction
        // Singleton-domain variables (genuine variables, domain size 1):
        // exercises the propagation path rather than constant folding.
        {pair{-4, -4}, pair{4, 4}}, // tautology
        {pair{-4, -4}, pair{5, 5}}, // contradiction
        // Mixed: one genuine constant, one real singleton-domain variable.
        {-6, pair{6, 6}},   // tautology
        {pair{-6, -6}, 7}}; // contradiction

    mt19937 rand(*get_seed());
    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_bounds(-10, 10, 5, 15), random_bounds(-10, 10, 5, 15));
    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_constant(-10, 10), random_bounds(-10, 10, 5, 15));
    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_bounds(-10, 10, 5, 15), random_constant(-10, 10));

    if (run_initialisers && can_run_veripb()) {
        // Each case isolates one of Abs::prepare's four consequence bounds.
        // The first failure aborts; comment out earlier cases as each one's
        // proof gets fixed. Run before the rest of the proof suite so the
        // failure is unambiguous — the random tests below also exercise these
        // bounds and will fail until the proofs are filled in.

        // Bound 1: v2 >= 0 — non-trivial (v2.lb < 0); other bounds trivial.
        run_abs_initialiser_test("bound1_v2_ge_0", {-3, 3}, {-2, 3});

        // Bound 2: v1 <= ub(v2) — non-trivial (v1.ub > v2.ub); others trivial.
        run_abs_initialiser_test("bound2_v1_le_ubv2", {-3, 5}, {0, 3});

        // Bound 3: v1 >= -ub(v2) — non-trivial (v1.lb < -v2.ub); others trivial.
        run_abs_initialiser_test("bound3_v1_ge_negubv2", {-5, 3}, {0, 3});

        // Bound 4: v2 <= max(ub(v1), -lb(v1)) — non-trivial (v2.ub > that max).
        run_abs_initialiser_test("bound4_v2_le_maxv1", {-3, 3}, {0, 5});

        // Wider domains that cross bit-encoding boundaries — the pol-step
        // shape mustn't rely on small bit widths happening to keep things
        // simple. Domains chosen to bracket powers of two (where the bit
        // encoding picks up an extra bit), and asymmetric ranges where M =
        // -lb(v1) ≠ ub(v1). UNSAT cases keep enumeration cheap.
        run_abs_initialiser_test("wide_8bit", {-32, 31}, {-16, 47});
        run_abs_initialiser_test("wide_just_over_8bit", {-33, 32}, {-16, 47});
        run_abs_initialiser_test("wide_unsat", {-50, 50}, {100, 200});
        run_abs_initialiser_test("wide_asym_lb_dominant", {-50, 5}, {0, 80});
        run_abs_initialiser_test("wide_asym_ub_dominant", {-5, 50}, {0, 80});
    }

    // Sparse-domain hole rows, keyed to the two interior loops. These run under
    // the view sweep as well as bare: since #931 a wrapped operand takes the
    // same interval path a plain one does, and these are the only rows in the
    // suite that reach either interior loop at all, so without them nothing
    // exercises a range removal over a view's own encoding.
    auto contiguous = [](int lo, int hi) {
        vector<int> result;
        for (int v = lo; v <= hi; ++v)
            result.push_back(v);
        return result;
    };
    vector<tuple<string, vector<int>, vector<int>>> hole_data = {// Image loop. v1's image is {0, 1} u [8, 10], so [2, 7] has no preimage
        // and is removed as one run of six. Nothing clips it first: v1 spans
        // zero, so neither lower bound moves, and the two upper bounds coincide.
        {"image_gap", {-1, 0, 1, 8, 9, 10}, contiguous(0, 10)},
        // The same image reached from below zero, so the reason's live literal
        // is the mirrored ~[v1 in -7..-2] rather than ~[v1 in 2..7].
        {"image_gap_neg", {-10, -9, -8, 0, 1}, contiguous(0, 10)},
        // An image run starting at zero, where the removed range and its mirror
        // overlap at zero. v1 keeps a negative value so that v2's lower bound is
        // not lifted past the run before the loop sees it.
        {"image_gap_from_zero", {-3, 3, 4, 5}, contiguous(0, 5)},
        // Preimage loop, with a run whose distance from zero is the point: the
        // sign the justification needs is 31 order atoms away from the bound the
        // conclusion's negation gives it. The random rows all leave runs
        // adjacent to zero, where that step is free.
        {"preimage_far", contiguous(-50, 50), {30, 40}}};

    // Bare-handle dup ranges. Skipped under the view-wrap sweep.
    vector<pair<int, int>> dup_data = {
        {-3, 3}, {-5, 0}, {0, 5}, {-1, 1}, {2, 5} //
    };

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & [r1, r2] : data)
            run_abs_test(proofs, view_cfg, r1, r2);
        for (auto & [label, v1_values, v2_values] : hole_data)
            run_abs_hole_test(proofs, view_cfg, label, v1_values, v2_values);
        if (view_wrap_config_is_effectively_bare(view_cfg, n_positions)) {
            for (auto & x_range : dup_data)
                run_dup_abs_test(proofs, x_range);
        }
    }

    return EXIT_SUCCESS;
}
