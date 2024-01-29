#include <gcs/constraints/constraints_test_utils.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
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
auto run_equals_test(const string & which, bool proofs, pair<int, int> v1_range, pair<int, int> v2_range, const function<auto(int, int, int)->bool> & is_satisfying) -> void
{
    print(cerr, "equals {} {} {} {}", which, v1_range, v2_range, proofs ? " with proofs:" : ":");
    cerr << flush;

    pair<int, int> v3_range{0, 1};
    set<tuple<int, int, int>> expected, actual;
    build_expected(expected, is_satisfying, v1_range, v2_range, v3_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = p.create_integer_variable(Integer(v1_range.first), Integer(v1_range.second));
    auto v2 = p.create_integer_variable(Integer(v2_range.first), Integer(v2_range.second));
    auto v3 = p.create_integer_variable(0_i, 1_i);
    if constexpr (is_same_v<Constraint_, Equals>) {
        p.post(Constraint_{v1, v2});
    }
    else {
        p.post(Constraint_{v1, v2, v3 == 1_i});
    }

    auto proof_name = proofs ? make_optional("equals_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2, v3});

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
        expected, [](int x, int y, int z, int c) -> bool {
            if (x == 4 && c != 0) return false;
            if (x == 5 && c != 0) return false;
            if (x == 6 && c != 0) return false;
            if (x == 9 && c != 0) return false;
            if (x == 10 && c != 0) return false;

            if (y == 1 && c != 0) return false;
            if (y == 2 && c != 0) return false;
            if (y == 3 && c != 0) return false;
            if (y == 6 && c != 0) return false;
            if (y == 7 && c != 0) return false;
            if (y == 8 && c != 0) return false;

            if (z == 1) {
                if (x != y) return false;
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
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{x, y, z, c});

    check_results(proof_name, expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<pair<pair<int, int>, pair<int, int>>> data = {
        {{2, 5}, {1, 6}},
        {{1, 6}, {2, 5}},
        {{1, 3}, {1, 3}},
        {{1, 5}, {6, 8}},
        {{1, 1}, {2, 4}},
        {{-2, -2}, {-2, -1}},
        {{1, 3}, {5, 8}},
        {{4, 13}, {3, 16}},
        {{-2, 4}, {-8, 7}},
        {{-7, 3}, {-10, 5}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_bounds(-10, 10, 5, 15), random_bounds(-10, 10, 5, 15));

    run_no_overlap_equals_test(false);
    for (auto & [r1, r2] : data) {
        run_equals_test<Equals>("equals", false, r1, r2, [](int a, int b, int) { return a == b; });
        run_equals_test<EqualsIf>("equals if", false, r1, r2, [](int a, int b, int f) { return (! f) || (a == b); });
        run_equals_test<EqualsIff>("equals iff", false, r1, r2, [](int a, int b, int f) { return (a == b) == f; });
    }

    if (can_run_veripb()) {
        run_no_overlap_equals_test(true);
        for (auto & [r1, r2] : data) {
            run_equals_test<Equals>("equals", true, r1, r2, [](int a, int b, int) { return a == b; });
            run_equals_test<EqualsIf>("equals if", true, r1, r2, [](int a, int b, int f) { return (! f) || (a == b); });
            run_equals_test<EqualsIff>("equals iff", true, r1, r2, [](int a, int b, int f) { return (a == b) == f; });
        }
    }

    return EXIT_SUCCESS;
}
