#include <gcs/constraints/constraints_test_utils.hh>
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
using std::random_device;
using std::set;
using std::string;
using std::to_string;
using std::tuple;
using std::uniform_int_distribution;
using std::vector;

using fmt::print;
using fmt::println;

using namespace gcs;
using namespace gcs::test_innards;

template <typename Constraint_>
auto run_linear_test(bool proofs, const string & mode, pair<int, int> v1_range, pair<int, int> v2_range,
    pair<int, int> v3_range, const vector<pair<vector<int>, int>> & ineqs,
    const std::function<auto(int, int)->bool> & compare) -> void
{
    print(cerr, "linear {} {} {} {} {} {}", mode, v1_range, v2_range, v3_range, ineqs, proofs ? " with proofs:" : ":");
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
    auto v1 = p.create_integer_variable(Integer(v1_range.first), Integer(v1_range.second));
    auto v2 = p.create_integer_variable(Integer(v2_range.first), Integer(v2_range.second));
    auto v3 = p.create_integer_variable(Integer(v3_range.first), Integer(v3_range.second));
    auto vs = vector{v1, v2, v3};
    for (auto & [linear, value] : ineqs) {
        WeightedSum c;
        for (const auto & [idx, coeff] : enumerate(linear))
            if (coeff != 0)
                c += Integer{coeff} * vs[idx];
        p.post(Constraint_{c, Integer{value}});
    }

    auto proof_name = proofs ? make_optional("linear_equality_test") : nullopt;

    if ((! is_same_v<Constraint_, LinearEquality>) && 1 == ineqs.size())
        solve_for_tests_checking_consistency(p, proof_name, expected, actual, tuple{pair{v1, CheckConsistency::BC}, pair{v2, CheckConsistency::BC}, pair{v3, CheckConsistency::BC}});
    else
        solve_for_tests(p, proof_name, actual, tuple{v1, v2, v3});

    check_results(proof_name, expected, actual);
}

template <typename Constraint_>
auto run_linear_reif_test(bool full_reif, bool proofs, const string & mode, pair<int, int> v1_range, pair<int, int> v2_range,
    pair<int, int> v3_range, const vector<pair<vector<int>, int>> & ineqs,
    const std::function<auto(int, int)->bool> & compare) -> void
{
    for (const auto & v4_range : vector<pair<int, int>>{{0, 0}, {1, 1}, {0, 1}}) {
        print(cerr, "linear {} {} {} {} {} {} {} {}", mode, full_reif ? "full_reif" : "half_reif",
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
        auto v1 = p.create_integer_variable(Integer(v1_range.first), Integer(v1_range.second));
        auto v2 = p.create_integer_variable(Integer(v2_range.first), Integer(v2_range.second));
        auto v3 = p.create_integer_variable(Integer(v3_range.first), Integer(v3_range.second));
        auto v4 = p.create_integer_variable(Integer(v4_range.first), Integer(v4_range.second));
        auto vs = vector{v1, v2, v3};
        for (auto & [linear, value] : ineqs) {
            WeightedSum c;
            for (const auto & [idx, coeff] : enumerate(linear))
                if (coeff != 0)
                    c += Integer{coeff} * vs[idx];
            p.post(Constraint_{c, Integer{value}, v4 == 1_i});
        }

        auto proof_name = proofs ? make_optional("linear_equality_test") : nullopt;

        if ((! is_same_v<Constraint_, LinearEqualityIff>) && 1 == ineqs.size() && v4_range.first == v4_range.second)
            solve_for_tests_checking_consistency(p, proof_name, expected, actual, tuple{pair{v1, CheckConsistency::BC}, pair{v2, CheckConsistency::BC}, pair{v3, CheckConsistency::BC}, pair{v4, CheckConsistency::None}});
        else
            solve_for_tests(p, proof_name, actual, tuple{v1, v2, v3, v4});

        check_results(proof_name, expected, actual);
    }
}

auto main(int, char *[]) -> int
{
    vector<tuple<pair<int, int>, pair<int, int>, pair<int, int>, vector<pair<vector<int>, int>>>> data;

    data.emplace_back(
        pair{0, 2}, pair{-2, 2}, pair{0, 5},
        vector{
            pair{vector{1, 2, 3}, 6}});

    data.emplace_back(
        pair{3, 8}, pair{-4, 7}, pair{2, 5},
        vector{
            pair{vector{2, 3, 4}, 20},
            pair{vector{-1, -3, 0}, -5},
            pair{vector{0, 4, 2}, 6}});

    data.emplace_back(
        pair{3, 8}, pair{-4, 7}, pair{2, 5},
        vector{
            pair{vector{2, 3, 4}, 30},
            pair{vector{-1, -3, 0}, -5},
            pair{vector{0, 4, 2}, 6}});

    data.emplace_back(
        pair{-3, 5}, pair{-3, 5}, pair{-2, 5},
        vector{
            pair{vector{2, 3, 4}, 20},
            pair{vector{-1, -3, 0}, -5},
            pair{vector{0, 4, 2}, 6}});

    data.emplace_back(
        pair{7, 9}, pair{-7, 0}, pair{4, 8},
        vector{
            pair{vector{-3, 3, -5}, -62},
            pair{vector{3, 4, 3}, 197}});

    data.emplace_back(
        pair{3, 4}, pair{8, 12}, pair{5, 13},
        vector{
            pair{vector{-8, -9, -6}, -154},
            pair{vector{8, -9, -9}, 71},
            pair{vector{8, 5, 9}, 175},
            pair{vector{3, -8, 10}, 9},
            pair{vector{6, 4, 5}, 174}});

    data.emplace_back(
        pair{-7, -6}, pair{-9, -2}, pair{-4, 3},
        vector{
            pair{vector{9, -9, -8}, 90},
            pair{vector{6, 1, -5}, 188},
            pair{vector{10, 8, -10}, 67},
            pair{vector{-2, -8, 0}, 138},
            pair{vector{10, 4, 7}, -78}});

    data.emplace_back(
        pair{8, 12}, pair{5, 11}, pair{-2, 4},
        vector{
            pair{vector{0, 0, 0}, -159}});

    data.emplace_back(
        pair{0, 1}, pair{0, 1}, pair{0, 1},
        vector{
            pair{vector{2, 2, 2}, 5}});

    data.emplace_back(
        pair{0, 1}, pair{0, 1}, pair{0, 1},
        vector{
            pair{vector{1, 1, 1}, 2}});

    data.emplace_back(
        pair{-7, 5}, pair{7, 12}, pair{-3, 12},
        vector{pair{vector{4, -8, 10}, 94}});

    random_device rand_dev;
    mt19937 rand(rand_dev());
    uniform_int_distribution nc_dist(1, 5);
    for (int x = 0; x < 5; ++x)
        generate_random_data(rand, data, random_bounds(-10, 10, 5, 15), random_bounds(-10, 10, 5, 15),
            random_bounds(-10, 10, 5, 15), vector(nc_dist(rand), pair{vector(3, uniform_int_distribution(-10, 10)), uniform_int_distribution(-200, 200)}));

    for (auto & [r1, r2, r3, constraints] : data) {
        run_linear_test<LinearEquality>(false, "eq", r1, r2, r3, constraints, [&](int a, int b) { return a == b; });
        run_linear_test<LinearNotEquals>(false, "ne", r1, r2, r3, constraints, [&](int a, int b) { return a != b; });
        run_linear_test<LinearLessThanEqual>(false, "le", r1, r2, r3, constraints, [&](int a, int b) { return a <= b; });
        run_linear_test<LinearGreaterThanEqual>(false, "ge", r1, r2, r3, constraints, [&](int a, int b) { return a >= b; });
        run_linear_reif_test<LinearGreaterThanEqualIf>(false, false, "ge", r1, r2, r3, constraints, [&](int a, int b) { return a >= b; });
        run_linear_reif_test<LinearLessThanEqualIf>(false, false, "le", r1, r2, r3, constraints, [&](int a, int b) { return a <= b; });
        run_linear_reif_test<LinearEqualityIff>(true, false, "eq", r1, r2, r3, constraints, [&](int a, int b) { return a == b; });
        run_linear_reif_test<LinearLessThanEqualIff>(true, false, "le", r1, r2, r3, constraints, [&](int a, int b) { return a <= b; });
        run_linear_reif_test<LinearGreaterThanEqualIff>(true, false, "ge", r1, r2, r3, constraints, [&](int a, int b) { return a >= b; });
    }

    if (can_run_veripb())
        for (auto & [r1, r2, r3, constraints] : data) {
            run_linear_test<LinearEquality>(true, "eq", r1, r2, r3, constraints, [&](int a, int b) { return a == b; });
            run_linear_test<LinearNotEquals>(true, "ne", r1, r2, r3, constraints, [&](int a, int b) { return a != b; });
            run_linear_test<LinearLessThanEqual>(true, "le", r1, r2, r3, constraints, [&](int a, int b) { return a <= b; });
            run_linear_test<LinearGreaterThanEqual>(true, "ge", r1, r2, r3, constraints, [&](int a, int b) { return a >= b; });
            run_linear_reif_test<LinearGreaterThanEqualIf>(false, true, "ge", r1, r2, r3, constraints, [&](int a, int b) { return a >= b; });
            run_linear_reif_test<LinearLessThanEqualIf>(false, true, "le", r1, r2, r3, constraints, [&](int a, int b) { return a <= b; });
            run_linear_reif_test<LinearEqualityIff>(true, true, "eq", r1, r2, r3, constraints, [&](int a, int b) { return a == b; });
            run_linear_reif_test<LinearLessThanEqualIff>(true, true, "le", r1, r2, r3, constraints, [&](int a, int b) { return a <= b; });
            run_linear_reif_test<LinearGreaterThanEqualIff>(true, true, "ge", r1, r2, r3, constraints, [&](int a, int b) { return a >= b; });
        }

    return EXIT_SUCCESS;
}
