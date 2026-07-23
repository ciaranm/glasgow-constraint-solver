#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <util/enumerate.hh>

#include <cstdlib>
#include <functional>
#include <iostream>
#include <random>
#include <set>
#include <tuple>
#include <type_traits>
#include <utility>
#include <vector>

using std::cerr;
using std::flush;
using std::is_same_v;
using std::make_optional;
using std::mt19937;
using std::nullopt;
using std::pair;
using std::set;
using std::string;
using std::tuple;
using std::uniform_int_distribution;
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

namespace
{
    // CI runs this test in both propagation modes (incremental / stateless) by setting
    // GCS_LINEAR_INCREMENTAL_THRESHOLD; tag the proof file names with it so the two
    // runs don't clobber each other's .opb/.pbp under parallel ctest.
    auto threshold_proof_suffix() -> string
    {
        if (const char * e = std::getenv("GCS_LINEAR_INCREMENTAL_THRESHOLD"))
            return string{"_t"} + e;
        return {};
    }
}

template <typename Constraint_>
auto run_linear_test(bool proofs, const string & mode, const ViewWrapConfig & view_cfg, pair<int, int> v1_range, pair<int, int> v2_range,
    pair<int, int> v3_range, const vector<pair<vector<int>, int>> & ineqs, const std::function<auto(int, int)->bool> & compare) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 3);
    print(cerr, "linear [{}] {} {} {} {} {} {}", view_wrap_config_label(view_cfg), mode, v1_range, v2_range, v3_range, ineqs,
        proofs ? " with proofs:" : ":");
    cerr << flush;

    auto is_satisfying = [&](int a, int b, int c) {
        for (auto & [linear, value] : ineqs)
            if (! compare(linear[0] * a + linear[1] * b + linear[2] * c, value))
                return false;
        return true;
    };

    set<tuple<int, int, int>> expected, actual;
    build_expected(expected, is_satisfying, v1_range, v2_range, v3_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = create_integer_variable_or_constant_with_view(p, v1_range, wraps.at(0));
    auto v2 = create_integer_variable_or_constant_with_view(p, v2_range, wraps.at(1));
    auto v3 = create_integer_variable_or_constant_with_view(p, v3_range, wraps.at(2));
    auto vs = vector<IntegerVariableID>{v1, v2, v3};
    for (auto & [linear, value] : ineqs) {
        WeightedSum c;
        for (const auto & [idx, coeff] : enumerate(linear))
            if (coeff != 0)
                c += Integer{coeff} * vs[idx];
        p.post(Constraint_{c, Integer{value}});
    }

    auto proof_name =
        proofs ? make_optional("linear_equality_test_" + mode + "_" + view_wrap_config_label(view_cfg) + threshold_proof_suffix()) : nullopt;

    if ((! is_same_v<Constraint_, LinearEquality>) && 1 == ineqs.size())
        solve_for_tests_checking_consistency(
            p, proof_name, expected, actual, tuple{pair{v1, CheckConsistency::BC}, pair{v2, CheckConsistency::BC}, pair{v3, CheckConsistency::BC}});
    else
        solve_for_tests(p, proof_name, actual, tuple{v1, v2, v3});

    check_results(proof_name, expected, actual);
}

template <typename Constraint_>
auto run_linear_test_gac(bool proofs, const string & mode, const ViewWrapConfig & view_cfg, pair<int, int> v1_range, pair<int, int> v2_range,
    pair<int, int> v3_range, const vector<pair<vector<int>, int>> & ineqs, const std::function<auto(int, int)->bool> & compare) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 3);
    print(cerr, "linear gac [{}] {} {} {} {} {} {}", view_wrap_config_label(view_cfg), mode, v1_range, v2_range, v3_range, ineqs,
        proofs ? " with proofs:" : ":");
    cerr << flush;

    auto is_satisfying = [&](int a, int b, int c) {
        for (auto & [linear, value] : ineqs)
            if (! compare(linear[0] * a + linear[1] * b + linear[2] * c, value))
                return false;
        return true;
    };

    set<tuple<int, int, int>> expected, actual;
    build_expected(expected, is_satisfying, v1_range, v2_range, v3_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = create_integer_variable_or_constant_with_view(p, v1_range, wraps.at(0));
    auto v2 = create_integer_variable_or_constant_with_view(p, v2_range, wraps.at(1));
    auto v3 = create_integer_variable_or_constant_with_view(p, v3_range, wraps.at(2));
    auto vs = vector<IntegerVariableID>{v1, v2, v3};
    for (auto & [linear, value] : ineqs) {
        WeightedSum c;
        for (const auto & [idx, coeff] : enumerate(linear))
            if (coeff != 0)
                c += Integer{coeff} * vs[idx];
        p.post(Constraint_{c, Integer{value}}.with_consistency(consistency::Tabulated{}));
    }

    auto proof_name =
        proofs ? make_optional("linear_equality_test_" + mode + "_" + view_wrap_config_label(view_cfg) + threshold_proof_suffix()) : nullopt;

    if (1 == ineqs.size())
        solve_for_tests_checking_consistency(p, proof_name, expected, actual,
            tuple{pair{v1, CheckConsistency::GAC}, pair{v2, CheckConsistency::GAC}, pair{v3, CheckConsistency::GAC}});
    else
        solve_for_tests(p, proof_name, actual, tuple{v1, v2, v3});

    check_results(proof_name, expected, actual);
}

template <typename Constraint_>
auto run_linear_reif_test(bool full_reif, bool proofs, const string & mode, const ViewWrapConfig & view_cfg, pair<int, int> v1_range,
    pair<int, int> v2_range, pair<int, int> v3_range, const vector<pair<vector<int>, int>> & ineqs,
    const std::function<auto(int, int)->bool> & compare) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 3);
    for (const auto & v4_range : vector<pair<int, int>>{{0, 0}, {1, 1}, {0, 1}}) {
        print(cerr, "linear [{}] {} {} {} {} {} {} {} {}", view_wrap_config_label(view_cfg), mode, full_reif ? "full_reif" : "half_reif", v1_range,
            v2_range, v3_range, v4_range, ineqs, proofs ? " with proofs:" : ":");
        cerr << flush;

        auto is_satisfying = [&](int a, int b, int c, int d) {
            set<bool> mismatches;
            for (auto & [linear, value] : ineqs) {
                mismatches.emplace(! compare(linear[0] * a + linear[1] * b + linear[2] * c, value));
            }
            if (mismatches.contains(false) && mismatches.contains(true))
                return ((! full_reif) && 0 == d);
            else if (mismatches.contains(true))
                return 0 == d;
            else
                return (! full_reif) || 1 == d;
        };

        set<tuple<int, int, int, int>> expected, actual;
        build_expected(expected, is_satisfying, v1_range, v2_range, v3_range, v4_range);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        auto v1 = create_integer_variable_or_constant_with_view(p, v1_range, wraps.at(0));
        auto v2 = create_integer_variable_or_constant_with_view(p, v2_range, wraps.at(1));
        auto v3 = create_integer_variable_or_constant_with_view(p, v3_range, wraps.at(2));
        auto v4 = p.create_integer_variable(Integer(v4_range.first), Integer(v4_range.second), "c");
        auto vs = vector<IntegerVariableID>{v1, v2, v3};
        for (auto & [linear, value] : ineqs) {
            WeightedSum c;
            for (const auto & [idx, coeff] : enumerate(linear))
                if (coeff != 0)
                    c += Integer{coeff} * vs[idx];
            p.post(Constraint_{c, Integer{value}, v4 == 1_i});
        }

        auto proof_name =
            proofs ? make_optional("linear_equality_test_" + mode + "_" + view_wrap_config_label(view_cfg) + threshold_proof_suffix()) : nullopt;

        if ((! is_same_v<Constraint_, LinearEqualityIff>) && (! is_same_v<Constraint_, LinearEqualityIf>) &&
            (! is_same_v<Constraint_, LinearNotEqualsIf>) && (! is_same_v<Constraint_, LinearNotEqualsIff>) && 1 == ineqs.size())
            solve_for_tests_checking_consistency(p, proof_name, expected, actual,
                tuple{
                    pair{v1, CheckConsistency::BC}, pair{v2, CheckConsistency::BC}, pair{v3, CheckConsistency::BC}, pair{v4, CheckConsistency::GAC}});
        else
            solve_for_tests(p, proof_name, actual, tuple{v1, v2, v3, v4});

        check_results(proof_name, expected, actual);
    }
}

// The tabulated flavour of the reified test: the same reified semantics, but
// posted with consistency::Tabulated, which enumerates the table in-proof with
// the condition variable's released values covered by wildcard tuples. That
// achieves GAC on the terms and the condition variable alike, so check it.
template <typename Constraint_>
auto run_linear_reif_test_gac(bool full_reif, bool proofs, const string & mode, const ViewWrapConfig & view_cfg, pair<int, int> v1_range,
    pair<int, int> v2_range, pair<int, int> v3_range, const vector<pair<vector<int>, int>> & ineqs,
    const std::function<auto(int, int)->bool> & compare) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 3);
    for (const auto & v4_range : vector<pair<int, int>>{{0, 0}, {1, 1}, {0, 1}}) {
        print(cerr, "linear gac [{}] {} {} {} {} {} {} {} {}", view_wrap_config_label(view_cfg), mode, full_reif ? "full_reif" : "half_reif",
            v1_range, v2_range, v3_range, v4_range, ineqs, proofs ? " with proofs:" : ":");
        cerr << flush;

        auto is_satisfying = [&](int a, int b, int c, int d) {
            set<bool> mismatches;
            for (auto & [linear, value] : ineqs) {
                mismatches.emplace(! compare(linear[0] * a + linear[1] * b + linear[2] * c, value));
            }
            if (mismatches.contains(false) && mismatches.contains(true))
                return ((! full_reif) && 0 == d);
            else if (mismatches.contains(true))
                return 0 == d;
            else
                return (! full_reif) || 1 == d;
        };

        set<tuple<int, int, int, int>> expected, actual;
        build_expected(expected, is_satisfying, v1_range, v2_range, v3_range, v4_range);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        auto v1 = create_integer_variable_or_constant_with_view(p, v1_range, wraps.at(0));
        auto v2 = create_integer_variable_or_constant_with_view(p, v2_range, wraps.at(1));
        auto v3 = create_integer_variable_or_constant_with_view(p, v3_range, wraps.at(2));
        auto v4 = p.create_integer_variable(Integer(v4_range.first), Integer(v4_range.second), "c");
        auto vs = vector<IntegerVariableID>{v1, v2, v3};
        for (auto & [linear, value] : ineqs) {
            WeightedSum c;
            for (const auto & [idx, coeff] : enumerate(linear))
                if (coeff != 0)
                    c += Integer{coeff} * vs[idx];
            p.post(Constraint_{c, Integer{value}, v4 == 1_i}.with_consistency(consistency::Tabulated{}));
        }

        auto proof_name =
            proofs ? make_optional("linear_equality_test_" + mode + "_gac_" + view_wrap_config_label(view_cfg) + threshold_proof_suffix()) : nullopt;

        if (1 == ineqs.size())
            solve_for_tests_checking_consistency(p, proof_name, expected, actual,
                tuple{pair{v1, CheckConsistency::GAC}, pair{v2, CheckConsistency::GAC}, pair{v3, CheckConsistency::GAC},
                    pair{v4, CheckConsistency::GAC}});
        else
            solve_for_tests(p, proof_name, actual, tuple{v1, v2, v3, v4});

        check_results(proof_name, expected, actual);
    }
}

// Dup-variable test: Linear with the same handle in two terms. The
// audit predicts the propagator coalesces via tidy_up_linear and the
// PB encoding sums coefficients in normal form. Consistency isn't
// checked on dup runs; see tmp/duplicate_var_audit.md.
template <typename Constraint_>
auto run_dup_linear_test(bool proofs, const string & mode, pair<int, int> a_range, pair<int, int> b_range, const vector<int> & coeffs_a_then_b,
    int rhs, const std::function<auto(int, int)->bool> & compare) -> void
{
    // coeffs_a_then_b has 3 entries; positions 0 and 1 use variable a,
    // position 2 uses variable b. Effective sum: (c0+c1)*a + c2*b.
    print(cerr, "linear dup {} a={} b={} coeffs={} rhs={}{}", mode, a_range, b_range, coeffs_a_then_b, rhs, proofs ? " with proofs:" : ":");
    cerr << flush;

    auto is_satisfying = [&](int av, int bv) {
        int sum = coeffs_a_then_b.at(0) * av + coeffs_a_then_b.at(1) * av + coeffs_a_then_b.at(2) * bv;
        return compare(sum, rhs);
    };

    set<tuple<int, int>> expected, actual;
    build_expected(expected, is_satisfying, a_range, b_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto a = p.create_integer_variable(Integer(a_range.first), Integer(a_range.second));
    auto b = p.create_integer_variable(Integer(b_range.first), Integer(b_range.second));
    WeightedSum c;
    c += Integer{coeffs_a_then_b.at(0)} * a;
    c += Integer{coeffs_a_then_b.at(1)} * a;
    c += Integer{coeffs_a_then_b.at(2)} * b;
    p.post(Constraint_{c, Integer{rhs}});

    auto proof_name = proofs ? make_optional("linear_equality_test_" + mode + "_dup" + threshold_proof_suffix()) : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{a, b});
    check_results(proof_name, expected, actual);
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    // Mode is the first non-flag positional; --view-* flags may follow. With no
    // mode given (a manual run rather than the ctest harness) run every mode.
    string requested_mode;
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (! a.starts_with("--")) {
            requested_mode = a;
            break;
        }
    }
    // Keep in sync with the if-chain below and the matching foreach(mode ...) in
    // gcs/CMakeLists.txt.
    const vector<string> all_modes = {"eq", "eq_if", "eq_iff", "ne", "ne_if", "ne_iff", "le", "le_if", "le_iff", "ge", "ge_if", "ge_iff"};
    const vector<string> modes = requested_mode.empty() ? all_modes : vector<string>{requested_mode};

    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    constexpr int n_positions = 3;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "linear view sweep: position {} out of range for n_positions = {}; skipping", *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    vector<tuple<pair<int, int>, pair<int, int>, pair<int, int>, vector<pair<vector<int>, int>>>> data;

    data.emplace_back(pair{0, 2}, pair{-2, 2}, pair{0, 5}, vector{pair{vector{1, 2, 3}, 6}});

    data.emplace_back(pair{3, 8}, pair{-4, 7}, pair{2, 5}, vector{pair{vector{2, 3, 4}, 20}, pair{vector{-1, -3, 0}, -5}, pair{vector{0, 4, 2}, 6}});

    data.emplace_back(pair{3, 8}, pair{-4, 7}, pair{2, 5}, vector{pair{vector{2, 3, 4}, 30}, pair{vector{-1, -3, 0}, -5}, pair{vector{0, 4, 2}, 6}});

    data.emplace_back(
        pair{-3, 5}, pair{-3, 5}, pair{-2, 5}, vector{pair{vector{2, 3, 4}, 20}, pair{vector{-1, -3, 0}, -5}, pair{vector{0, 4, 2}, 6}});

    data.emplace_back(pair{7, 9}, pair{-7, 0}, pair{4, 8}, vector{pair{vector{-3, 3, -5}, -62}, pair{vector{3, 4, 3}, 197}});

    data.emplace_back(pair{3, 4}, pair{8, 12}, pair{5, 13},
        vector{pair{vector{-8, -9, -6}, -154}, pair{vector{8, -9, -9}, 71}, pair{vector{8, 5, 9}, 175}, pair{vector{3, -8, 10}, 9},
            pair{vector{6, 4, 5}, 174}});

    data.emplace_back(pair{-7, -6}, pair{-9, -2}, pair{-4, 3},
        vector{pair{vector{9, -9, -8}, 90}, pair{vector{6, 1, -5}, 188}, pair{vector{10, 8, -10}, 67}, pair{vector{-2, -8, 0}, 138},
            pair{vector{10, 4, 7}, -78}});

    data.emplace_back(pair{8, 12}, pair{5, 11}, pair{-2, 4}, vector{pair{vector{0, 0, 0}, -159}});

    data.emplace_back(pair{0, 1}, pair{0, 1}, pair{0, 1}, vector{pair{vector{2, 2, 2}, 5}});

    data.emplace_back(pair{0, 1}, pair{0, 1}, pair{0, 1}, vector{pair{vector{1, 1, 1}, 2}});

    // {0,1}-domain variables carrying NEGATIVE coefficients, alongside a wider
    // variable so a bound is actually pushed: the bound justification
    // (justify_linear_bounds) then substitutes a negative-coefficient lower/upper
    // bound atom on a {0,1} variable -- the shape issue #554 was about, where a
    // bit-aliased >= 1 atom cancelled its term in the bound pol. The random
    // generator never produces width-1 domains, so this is only reached here.
    data.emplace_back(pair{0, 1}, pair{0, 1}, pair{0, 5}, vector{pair{vector{-2, -3, 1}, 0}});

    data.emplace_back(pair{0, 1}, pair{0, 1}, pair{-5, 0}, vector{pair{vector{-2, 3, -1}, 0}});

    data.emplace_back(pair{0, 1}, pair{2, 6}, pair{0, 1}, vector{pair{vector{-4, 1, -2}, -1}});

    data.emplace_back(pair{-7, 5}, pair{7, 12}, pair{-3, 12}, vector{pair{vector{4, -8, 10}, 94}});

    data.emplace_back(pair{8, 14}, pair{0, 8}, pair{4, 19}, vector{pair{vector{-7, 6, 7}, 69}});

    mt19937 rand(*get_seed());
    uniform_int_distribution nc_dist(1, 5);
    for (int x = 0; x < 5; ++x)
        generate_random_data(rand, data, random_bounds(-10, 10, 5, 15), random_bounds(-10, 10, 5, 15), random_bounds(-10, 10, 5, 15),
            vector(nc_dist(rand), pair{vector(3, uniform_int_distribution(-10, 10)), uniform_int_distribution(-200, 200)}));

    for (const auto & mode : modes) {
        for (bool proofs : {false, true}) {
            if (proofs && ! can_run_veripb())
                continue;
            for (auto & [r1, r2, r3, constraints] : data) {
                if (mode == "eq") {
                    run_linear_test<LinearEquality>(proofs, mode, view_cfg, r1, r2, r3, constraints, [&](int a, int b) { return a == b; });
                    run_linear_test_gac<LinearEquality>(proofs, mode, view_cfg, r1, r2, r3, constraints, [&](int a, int b) { return a == b; });
                }
                else if (mode == "eq_if") {
                    run_linear_reif_test<LinearEqualityIf>(
                        false, proofs, mode, view_cfg, r1, r2, r3, constraints, [&](int a, int b) { return a == b; });
                    run_linear_reif_test_gac<LinearEqualityIf>(
                        false, proofs, mode, view_cfg, r1, r2, r3, constraints, [&](int a, int b) { return a == b; });
                }
                else if (mode == "eq_iff") {
                    run_linear_reif_test<LinearEqualityIff>(
                        true, proofs, mode, view_cfg, r1, r2, r3, constraints, [&](int a, int b) { return a == b; });
                    run_linear_reif_test_gac<LinearEqualityIff>(
                        true, proofs, mode, view_cfg, r1, r2, r3, constraints, [&](int a, int b) { return a == b; });
                }
                else if (mode == "ne") {
                    run_linear_test<LinearNotEquals>(proofs, mode, view_cfg, r1, r2, r3, constraints, [&](int a, int b) { return a != b; });
                    run_linear_test_gac<LinearNotEquals>(proofs, mode, view_cfg, r1, r2, r3, constraints, [&](int a, int b) { return a != b; });
                }
                else if (mode == "ne_if") {
                    run_linear_reif_test<LinearNotEqualsIf>(
                        false, proofs, mode, view_cfg, r1, r2, r3, constraints, [&](int a, int b) { return a != b; });
                    run_linear_reif_test_gac<LinearNotEqualsIf>(
                        false, proofs, mode, view_cfg, r1, r2, r3, constraints, [&](int a, int b) { return a != b; });
                }
                else if (mode == "ne_iff") {
                    run_linear_reif_test<LinearNotEqualsIff>(
                        true, proofs, mode, view_cfg, r1, r2, r3, constraints, [&](int a, int b) { return a != b; });
                    run_linear_reif_test_gac<LinearNotEqualsIff>(
                        true, proofs, mode, view_cfg, r1, r2, r3, constraints, [&](int a, int b) { return a != b; });
                }
                else if (mode == "le") {
                    run_linear_test<LinearLessThanEqual>(proofs, mode, view_cfg, r1, r2, r3, constraints, [&](int a, int b) { return a <= b; });
                }
                else if (mode == "le_if") {
                    run_linear_reif_test<LinearLessThanEqualIf>(
                        false, proofs, mode, view_cfg, r1, r2, r3, constraints, [&](int a, int b) { return a <= b; });
                }
                else if (mode == "le_iff") {
                    run_linear_reif_test<LinearLessThanEqualIff>(
                        true, proofs, mode, view_cfg, r1, r2, r3, constraints, [&](int a, int b) { return a <= b; });
                }
                else if (mode == "ge") {
                    run_linear_test<LinearGreaterThanEqual>(proofs, mode, view_cfg, r1, r2, r3, constraints, [&](int a, int b) { return a >= b; });
                }
                else if (mode == "ge_if") {
                    run_linear_reif_test<LinearGreaterThanEqualIf>(
                        false, proofs, mode, view_cfg, r1, r2, r3, constraints, [&](int a, int b) { return a >= b; });
                }
                else if (mode == "ge_iff") {
                    run_linear_reif_test<LinearGreaterThanEqualIff>(
                        true, proofs, mode, view_cfg, r1, r2, r3, constraints, [&](int a, int b) { return a >= b; });
                }
                else
                    throw UnimplementedException{};
            }

            // Dup-variable cases. Cover the non-reified Linear variants;
            // reified forms share the same coalescing infrastructure.
            if (view_wrap_config_is_effectively_bare(view_cfg, n_positions)) {
                // 2*a + 3*a + 1*b coalesces to 5*a + 1*b.
                if (mode == "eq")
                    run_dup_linear_test<LinearEquality>(proofs, mode, {0, 5}, {-5, 5}, {2, 3, 1}, 10, [](int a, int b) { return a == b; });
                else if (mode == "ne")
                    run_dup_linear_test<LinearNotEquals>(proofs, mode, {0, 5}, {-5, 5}, {2, 3, 1}, 10, [](int a, int b) { return a != b; });
                else if (mode == "le")
                    run_dup_linear_test<LinearLessThanEqual>(proofs, mode, {0, 5}, {-5, 5}, {2, 3, 1}, 10, [](int a, int b) { return a <= b; });
                else if (mode == "ge")
                    run_dup_linear_test<LinearGreaterThanEqual>(proofs, mode, {0, 5}, {-5, 5}, {2, 3, 1}, 10, [](int a, int b) { return a >= b; });
                // 1*a + (-1)*a + 2*b coalesces to 0*a + 2*b = 2*b — exercises
                // the zero-coefficient-after-coalescing path.
                if (mode == "eq")
                    run_dup_linear_test<LinearEquality>(proofs, mode, {0, 5}, {0, 5}, {1, -1, 2}, 4, [](int a, int b) { return a == b; });
            }
        }
    }

    return EXIT_SUCCESS;
}
