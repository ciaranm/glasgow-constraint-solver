#include <gcs/constraints/constraints_test_utils.hh>
#include <gcs/constraints/logical.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <functional>
#include <iostream>
#include <optional>
#include <random>
#include <set>
#include <tuple>
#include <utility>
#include <vector>

using std::cerr;
using std::flush;
using std::function;
using std::make_optional;
using std::mt19937;
using std::nullopt;
using std::optional;
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

template <typename Logical_>
auto run_logical_test(const string & which, bool proofs, const vector<pair<int, int>> & vars, pair<int, int> full_reif,
    const function<auto(const vector<int> &, int)->bool> & is_satisfying) -> void
{
    print(cerr, "logical {} {} {} {}", which, vars, full_reif, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<pair<vector<int>, int>> expected, actual;
    build_expected(expected, is_satisfying, vars, full_reif);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> vs;
    for (const auto & [l, u] : vars)
        vs.emplace_back(p.create_integer_variable(Integer(l), Integer(u)));
    auto r = p.create_integer_variable(Integer(full_reif.first), Integer(full_reif.second));

    if (-1 == full_reif.first && -1 == full_reif.second)
        p.post(Logical_{vs});
    else
        p.post(Logical_{vs, r});

    auto proof_name = proofs ? make_optional("logical_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{vs, r});

    check_results(proof_name, expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<tuple<vector<pair<int, int>>, pair<int, int>>> data = {
        {{{0, 1}, {0, 1}, {0, 1}}, {0, 1}},
        {{{0, 1}, {0, 1}, {0, 1}}, {-1, -1}},
        {{{0, 1}, {1, 1}, {0, 1}}, {0, 1}},
        {{{0, 1}, {0, 0}, {0, 1}}, {0, 1}},
        {{{2, 5}, {-2, -1}, {1, 3}, {2, 5}}, {0, 2}},
        {{{2, 5}, {2, 5}}, {0, 0}},
        {{{-2, 1}, {2, 5}, {-2, 1}, {2, 5}}, {-1, 1}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());
    uniform_int_distribution n_values_dist(1, 4);
    for (int x = 0; x < 10; ++x) {
        auto n_values = n_values_dist(rand);
        generate_random_data(rand, data, vector(n_values, random_bounds(-2, 2, 1, 3)), random_bounds(-1, 1, 0, 3));
    }

    for (auto & [r1d, r2d] : data) {
        auto r1 = r1d; // clang
        auto r2 = r2d;
        run_logical_test<And>("and", false, r1, r2, [&](const vector<int> & v, int r) {
            bool result = true;
            for (auto & i : v)
                result = result && (i != 0);
            if (r2 == pair{-1, -1})
                return result;
            else
                return result == (r != 0);
        });
        run_logical_test<Or>("or", false, r1, r2, [&](const vector<int> & v, int r) {
            bool result = false;
            for (auto & i : v)
                result = result || (i != 0);
            if (r2 == pair{-1, -1})
                return result;
            else
                return result == (r != 0);
        });
    }

    if (can_run_veripb())
        for (auto & [r1d, r2d] : data) {
            auto r1 = r1d; // clang
            auto r2 = r2d;
            run_logical_test<And>("and", true, r1, r2, [&](const vector<int> & v, int r) {
                bool result = true;
                for (auto & i : v)
                    result = result && (i != 0);
                if (r2 == pair{-1, -1})
                    return result;
                else
                    return result == (r != 0);
            });
            run_logical_test<Or>("or", true, r1, r2, [&](const vector<int> & v, int r) {
                bool result = false;
                for (auto & i : v)
                    result = result || (i != 0);
                if (r2 == pair{-1, -1})
                    return result;
                else
                    return result == (r != 0);
            });
        }

    return EXIT_SUCCESS;
}
