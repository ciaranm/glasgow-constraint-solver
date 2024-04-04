#include <gcs/constraints/constraints_test_utils.hh>
#include <gcs/constraints/parity.hh>
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

auto run_parity_test(bool proofs, const vector<pair<int, int>> & array_range) -> void
{
    print(cerr, "parity odd {} {}", array_range, proofs ? " with proofs:" : ":");
    cerr << flush;

    auto is_satisfying = [](const vector<int> & a) {
        return count_if(a.begin(), a.end(), [](int x) { return x != 0; }) % 2 == 1;
    };

    set<tuple<vector<int>>> expected, actual;
    build_expected(expected, is_satisfying, array_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> array;
    for (const auto & [l, u] : array_range)
        array.push_back(p.create_integer_variable(Integer(l), Integer(u)));
    p.post(ParityOdd{array});

    auto proof_name = proofs ? make_optional("parity_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{array});

    check_results(proof_name, expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<vector<pair<int, int>>> data = {
        {{{0, 1}}},
        {{{0, 1}, {0, 1}}},
        {{{0, 1}, {0, 1}, {0, 1}}},
        {{{0, 1}, {0, 1}, {0, 1}, {0, 1}}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution n_values_dist(1, 4);
        auto n_values = n_values_dist(rand);
        generate_random_data(rand, data, vector{size_t(n_values), random_bounds(-1, 1, 0, 1)});
    }

    for (auto & v : data)
        run_parity_test(false, v);

    if (can_run_veripb())
        for (auto & v : data)
            run_parity_test(true, v);

    return EXIT_SUCCESS;
}
