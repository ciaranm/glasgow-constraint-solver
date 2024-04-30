#include <gcs/constraints/constraints_test_utils.hh>
#include <gcs/constraints/inverse.hh>
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
using std::cmp_not_equal;
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

auto run_inverse_test(bool proofs, const vector<pair<int, int>> & x_range, const vector<pair<int, int>> & y_range) -> void
{
    print(cerr, "inverse {} {} {}", x_range, y_range, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<vector<int>, vector<int>>> expected, actual;
    build_expected(
        expected, [&](const vector<int> & x, const vector<int> & y) {
            for (const auto & [i, _] : enumerate(x))
                if (cmp_not_equal(y.at(x.at(i)), i))
                    return false;
            for (const auto & [i, _] : enumerate(y))
                if (cmp_not_equal(x.at(y.at(i)), i))
                    return false;

            return true;
        },
        x_range, y_range);

    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> x, y;
    for (const auto & [l, u] : x_range)
        x.push_back(p.create_integer_variable(Integer(l), Integer(u)));
    for (const auto & [l, u] : y_range)
        y.push_back(p.create_integer_variable(Integer(l), Integer(u)));
    p.post(Inverse{x, y});

    auto proof_name = proofs ? make_optional("inverse_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{x, y});

    check_results(proof_name, expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<tuple<vector<pair<int, int>>, vector<pair<int, int>>>> var_data = {
        {{{0, 2}, {0, 2}, {0, 2}}, {{0, 2}, {0, 2}, {0, 2}}},
        {{{0, 2}, {1, 3}, {0, 2}, {0, 3}}, {{0, 3}, {1, 2}, {1, 3}, {0, 3}}},
        {{{0, 2}, {0, 2}, {0, 2}, {0, 4}, {0, 4}}, {{0, 4}, {0, 4}, {0, 4}, {3, 4}, {3, 4}}}};

    for (auto & [x, y] : var_data)
        run_inverse_test(false, x, y);

    if (can_run_veripb())
        for (auto & [x, y] : var_data)
            run_inverse_test(true, x, y);

    return EXIT_SUCCESS;
}
