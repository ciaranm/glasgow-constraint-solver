#include <gcs/constraints/constraints_test_utils.hh>
#include <gcs/constraints/element.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <util/enumerate.hh>

#include <cstdlib>
#include <functional>
#include <iostream>
#include <optional>
#include <random>
#include <set>
#include <tuple>
#include <utility>
#include <vector>

#include <fmt/core.h>
#include <fmt/ostream.h>
#include <fmt/ranges.h>

using std::cerr;
using std::cmp_less;
using std::flush;
using std::function;
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

auto run_element_test(bool proofs, pair<int, int> var_range, pair<int, int> idx_range, const vector<pair<int, int>> & array_range) -> void
{
    print(cerr, "element {} {} {} {}", var_range, idx_range, array_range, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, int, vector<int>>> expected, actual;
    build_expected(
        expected, [&](int v, int x, const vector<int> & a) {
            return x >= 0 && cmp_less(x, a.size()) && a.at(x) == v;
        },
        var_range, idx_range, array_range);

    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto var = p.create_integer_variable(Integer(var_range.first), Integer(var_range.second), "var");
    auto idx = p.create_integer_variable(Integer(idx_range.first), Integer(idx_range.second), "idx");
    vector<IntegerVariableID> array;
    for (const auto & [l, u] : array_range)
        array.push_back(p.create_integer_variable(Integer(l), Integer(u)));
    p.post(Element{var, idx, array});

    auto proof_name = proofs ? make_optional("element_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{var, idx, array});

    check_results(proof_name, expected, actual);
}

auto run_element_constant_test(bool proofs, pair<int, int> var_range, pair<int, int> idx_range, const vector<int> & array) -> void
{
    print(cerr, "element constant {} {} {} {}", var_range, idx_range, array, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, int>> expected, actual;
    build_expected(
        expected, [&](int v, int x) {
            return x >= 0 && cmp_less(x, array.size()) && array.at(x) == v;
        },
        var_range, idx_range);

    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto var = p.create_integer_variable(Integer(var_range.first), Integer(var_range.second), "var");
    auto idx = p.create_integer_variable(Integer(idx_range.first), Integer(idx_range.second), "idx");
    vector<Integer> a;
    for (const auto & v : array)
        a.push_back(Integer(v));
    p.post(ElementConstantArray{var, idx, &a});

    auto proof_name = proofs ? make_optional("element_test") : nullopt;
    solve_for_tests_checking_consistency(p, proof_name, expected, actual,
        tuple{pair{var, CheckConsistency::BC}, pair{idx, CheckConsistency::GAC}});

    check_results(proof_name, expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<tuple<pair<int, int>, pair<int, int>, vector<pair<int, int>>>> var_data = {
        {{1, 2}, {0, 1}, {{1, 2}, {1, 2}}},
        {{1, 2}, {-2, 2}, {{1, 2}, {1, 2}}},
        {{1, 2}, {0, 1}, {{1, 2}, {1, 2}, {1, 2}}},
        {{-1, 3}, {0, 2}, {{-1, 2}, {1, 3}, {4, 5}}},
        {{1, 4}, {0, 4}, {{1, 4}, {2, 3}, {0, 5}, {-2, 0}, {5, 7}}},
        {{-5, 5}, {-3, 2}, {{-8, 0}, {4, 4}, {10, 10}, {2, 11}, {4, 10}}},
        {{7, 10}, {0, 9}, {{8, 18}, {9, 19}, {-1, 0}, {-6, 0}}}};

    vector<tuple<pair<int, int>, pair<int, int>, vector<int>>> const_data = {
        {{1, 2}, {1, 2}, {1, 2}},
        {{1, 2}, {0, 1}, {1, 2}},
        {{1, 2}, {0, 2}, {1, 2, 2}},
        {{1, 2}, {0, 2}, {1, 2, 5}},
        {{-4, 6}, {-3, 3}, {-7, 2, -4, -10}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());

    uniform_int_distribution n_values_dist(1, 4);
    for (int x = 0; x < 10; ++x) {
        auto n_values = n_values_dist(rand);
        generate_random_data(rand, var_data, random_bounds(-10, 10, 5, 15), random_bounds(-10, 10, 0, 10),
            vector{size_t(n_values), random_bounds(-10, 10, 5, 15)});
    }

    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution values_dist(-10, 10);
        auto n_values = n_values_dist(rand);
        generate_random_data(rand, const_data, random_bounds(-10, 10, 5, 15), random_bounds(-10, 10, 0, 10),
            vector{size_t(n_values), values_dist});
    }

    for (auto & [r1, r2, r3] : var_data)
        run_element_test(false, r1, r2, r3);

    if (can_run_veripb())
        for (auto & [r1, r2, r3] : var_data)
            run_element_test(true, r1, r2, r3);

    for (auto & [r1, r2, r3] : const_data)
        run_element_constant_test(false, r1, r2, r3);

    if (can_run_veripb())
        for (auto & [r1, r2, r3] : const_data)
            run_element_constant_test(true, r1, r2, r3);

    return EXIT_SUCCESS;
}
