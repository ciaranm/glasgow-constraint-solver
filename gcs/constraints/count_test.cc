#include <gcs/constraints/count.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
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
using std::random_device;
using std::set;
using std::string;
using std::tuple;
using std::uniform_int_distribution;
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

auto run_count_test(bool proofs, const ViewWrapConfig & view_cfg,
    variant<int, pair<int, int>> result_range, variant<int, pair<int, int>> voi_range,
    const vector<variant<int, pair<int, int>>> & array_range) -> void
{
    // Position 0 = result, 1 = voi, 2..N+1 = array entries.
    int n_positions = 2 + static_cast<int>(array_range.size());
    auto wraps = wraps_for_positions(view_cfg, n_positions);
    visit([&](auto result, auto voi) { print(cerr, "count [{}] {} {} {} {}", view_wrap_config_label(view_cfg), result, voi, array_range, proofs ? " with proofs:" : ":"); }, result_range, voi_range);
    cerr << flush;

    auto is_satisfying = [](int v, int n, const vector<int> & a) {
        return n == count(a.begin(), a.end(), v);
    };

    set<tuple<int, int, vector<int>>> expected, actual;
    build_expected(expected, is_satisfying, voi_range, result_range, array_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto result = visit([&](auto r) { return create_integer_variable_or_constant_with_view(p, r, wraps.at(0)); }, result_range);
    auto voi = visit([&](auto v) { return create_integer_variable_or_constant_with_view(p, v, wraps.at(1)); }, voi_range);
    vector<IntegerVariableID> array;
    for (std::size_t i = 0; i < array_range.size(); ++i)
        array.push_back(visit([&](auto e) { return create_integer_variable_or_constant_with_view(p, e, wraps.at(i + 2)); }, array_range[i]));
    p.post(Count{array, voi, result});

    auto proof_name = proofs ? make_optional("count_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    // The Count propagator is GAC on the value-of-interest but only
    // bounds-consistent on how_many: it tightens how_many's bounds from the
    // achievable-count range but does not remove interior unsupported counts.
    // Those holes are real when the achievable counts are non-contiguous
    // (e.g. array [9,9], voi in [6,15] gives counts {0,2}, so how_many=1 is
    // unsupported but stays within [0,2]). Check how_many at BC accordingly.
    solve_for_tests_checking_consistency(p, proof_name, expected, actual, tuple{pair{voi, CheckConsistency::GAC}, pair{result, CheckConsistency::BC}, pair{array, CheckConsistency::None}});

    check_results(proof_name, expected, actual);
}

// Dup-variable test: Count with the same handle appearing in several
// array positions. Each occurrence is counted independently. Consistency
// isn't checked on dup runs; see tmp/duplicate_var_audit.md.
auto run_dup_count_test(bool proofs, const vector<pair<int, int>> & unique_domains,
    const vector<int> & positions, int voi_const, pair<int, int> result_range) -> void
{
    print(cerr, "count dup domains={} positions={} voi={} result={}{}",
        unique_domains, positions, voi_const, result_range, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, vector<int>>> expected, actual;
    build_expected(
        expected, [&](int r, const vector<int> & vals) -> bool {
            int counted = 0;
            for (auto pos : positions)
                if (vals.at(pos) == voi_const) ++counted;
            return r == counted;
        },
        result_range, unique_domains);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto result = p.create_integer_variable(Integer(result_range.first), Integer(result_range.second));
    vector<IntegerVariableID> unique_vars;
    for (const auto & d : unique_domains)
        unique_vars.push_back(p.create_integer_variable(Integer(d.first), Integer(d.second)));
    vector<IntegerVariableID> array;
    for (auto pos : positions)
        array.push_back(unique_vars.at(pos));
    p.post(Count{array, ConstantIntegerVariableID{Integer(voi_const)}, result});

    auto proof_name = proofs ? make_optional("count_test_dup") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{result, unique_vars});
    check_results(proof_name, expected, actual);
}

// result variable also appears in the array.
auto run_count_result_in_array_test(bool proofs, pair<int, int> shared_range, int voi_const) -> void
{
    print(cerr, "count result-in-array shared={} voi={}{}", shared_range, voi_const, proofs ? " with proofs:" : ":");
    cerr << flush;

    // Array is [shared] with result = shared: result = [shared == voi_const],
    // since the array has one entry and we count matches against voi_const.
    set<tuple<int>> expected, actual;
    build_expected(
        expected, [&](int s) -> bool {
            int hits = (s == voi_const) ? 1 : 0;
            return s == hits;
        },
        shared_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto shared = p.create_integer_variable(Integer(shared_range.first), Integer(shared_range.second));
    p.post(Count{vector<IntegerVariableID>{shared}, ConstantIntegerVariableID{Integer(voi_const)}, shared});

    auto proof_name = proofs ? make_optional("count_test_resin") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{shared});
    check_results(proof_name, expected, actual);
}

auto main(int argc, char * argv[]) -> int
{
    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    constexpr int n_positions = 6;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "count view sweep: position {} out of range for n_positions = {}; skipping",
            *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    using ArrayEntry = variant<int, pair<int, int>>;
    vector<tuple<variant<int, pair<int, int>>, variant<int, pair<int, int>>, vector<ArrayEntry>>> data = {
        {pair{1, 2}, pair{1, 2}, {pair{1, 2}, pair{1, 2}}},
        {pair{1, 2}, pair{0, 3}, {pair{1, 2}, pair{1, 2}}},
        {pair{1, 2}, pair{1, 2}, {pair{1, 2}, pair{1, 2}, pair{1, 2}}},
        {pair{0, 3}, pair{1, 2}, {pair{1, 2}, pair{1, 2}, pair{1, 2}}},
        {pair{0, 4}, pair{0, 4}, {pair{1, 2}, pair{1, 2}, pair{1, 2}}},
        {pair{1, 3}, pair{1, 6}, {pair{0, 4}, pair{0, 5}, pair{0, 6}}},
        {pair{-1, 3}, pair{0, 5}, {pair{-1, 2}, pair{1, 3}, pair{4, 5}}},
        {pair{1, 4}, pair{-3, 8}, {pair{1, 4}, pair{2, 3}, pair{0, 5}, pair{-2, 0}, pair{5, 7}}},
        {pair{0, 4}, pair{-5, 2}, {pair{7, 14}, pair{7, 11}}},
        {pair{3, 10}, pair{3, 8}, {pair{-2, 2}, pair{3, 7}, pair{5, 9}, pair{0, 6}}},
        {pair{1, 9}, pair{-5, 5}, {pair{2, 6}, pair{8, 11}, pair{6, 12}, pair{-3, 0}}},
        {pair{2, 2}, pair{3, 6}, {pair{5, 9}, pair{-5, 3}, pair{2, 6}}},
        // Constant array entries: voi seen N times where some array slots are fixed.
        {pair{0, 3}, pair{0, 3}, {1, 2, pair{1, 3}}},
        {pair{0, 3}, 2, {pair{1, 4}, 2, pair{1, 4}, 2}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution n_values_dist(1, 4);
        auto n_values = n_values_dist(rand);
        generate_random_data(rand, data, random_bounds(-7, 7, 5, 10), random_bounds(-7, 7, 5, 10),
            vector{size_t(n_values), random_bounds_or_constant(-5, 8, 3, 8)});
    }

    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution n_values_dist(1, 4);
        auto n_values = n_values_dist(rand);
        generate_random_data(rand, data, random_constant(-7, 7), random_bounds(-7, 7, 5, 10),
            vector{size_t(n_values), random_bounds_or_constant(-5, 8, 3, 8)});
    }

    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution n_values_dist(1, 4);
        auto n_values = n_values_dist(rand);
        generate_random_data(rand, data, random_constant(-7, 7), random_constant(-7, 7),
            vector{size_t(n_values), random_bounds_or_constant(-5, 8, 3, 8)});
    }

    bool run_dup = view_wrap_config_is_effectively_bare(view_cfg, n_positions);

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & [r1, r2, r3] : data)
            run_count_test(proofs, view_cfg, r1, r2, r3);
        if (run_dup) {
            // {x, x, y} — x's match counts twice.
            run_dup_count_test(proofs, {{1, 4}, {1, 4}}, {0, 0, 1}, 2, {0, 3});
            // {x, y, x} — non-adjacent dup (exercises the SmartTable hazard
            // pattern; Count's encoding shouldn't be affected, audit predicted OK).
            run_dup_count_test(proofs, {{1, 4}, {1, 4}}, {0, 1, 0}, 2, {0, 3});
            // {x, x} — count must be 0 or 2.
            run_dup_count_test(proofs, {{0, 3}}, {0, 0}, 2, {0, 2});

            // result variable also in array.
            run_count_result_in_array_test(proofs, {0, 2}, 0);
            run_count_result_in_array_test(proofs, {0, 2}, 1);
        }
    }

    return EXIT_SUCCESS;
}
