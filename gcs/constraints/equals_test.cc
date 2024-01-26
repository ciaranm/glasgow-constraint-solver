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

auto main(int, char *[]) -> int
{
    vector<pair<pair<int, int>, pair<int, int>>> data = {
        {{2, 5}, {1, 6}},
        {{1, 6}, {2, 5}},
        {{1, 3}, {1, 3}},
        {{1, 5}, {6, 8}},
        {{1, 1}, {2, 4}},
        {{-2, -2}, {-2, -1}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x)
        generate_random_data(rand, data, random_bounds(-10, 10, 5, 15), random_bounds(-10, 10, 5, 15));

    for (auto & [r1, r2] : data) {
        run_equals_test<Equals>("equals", false, r1, r2, [](int a, int b, int) { return a == b; });
        run_equals_test<EqualsIf>("equals if", false, r1, r2, [](int a, int b, int f) { return (! f) || (a == b); });
        run_equals_test<EqualsIff>("equals iff", false, r1, r2, [](int a, int b, int f) { return (a == b) == f; });
    }

    if (can_run_veripb())
        for (auto & [r1, r2] : data) {
            run_equals_test<Equals>("equals", true, r1, r2, [](int a, int b, int) { return a == b; });
            run_equals_test<EqualsIf>("equals if", true, r1, r2, [](int a, int b, int f) { return (! f) || (a == b); });
            run_equals_test<EqualsIff>("equals iff", true, r1, r2, [](int a, int b, int f) { return (a == b) == f; });
        }

    return EXIT_SUCCESS;
}
