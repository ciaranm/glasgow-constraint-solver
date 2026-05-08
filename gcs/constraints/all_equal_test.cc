#include <gcs/constraints/all_equal.hh>
#include <gcs/constraints/in.hh>
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
using std::tuple;
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

auto run_test(bool proofs, const vector<pair<int, int>> & domains) -> void
{
    print(cerr, "all_equal domains={}{}",
        domains, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<vector<int>>> expected, actual;
    build_expected(expected, [](const vector<int> & vs) {
        for (size_t i = 1; i < vs.size(); ++i)
            if (vs[i] != vs[0])
                return false;
        return true;
    },
        domains);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> vars;
    for (const auto & d : domains)
        vars.push_back(p.create_integer_variable(Integer(d.first), Integer(d.second)));
    p.post(AllEqual{vars});

    auto proof_name = proofs ? make_optional("all_equal_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{vars});
    check_results(proof_name, expected, actual);
}

auto run_holes_test(bool proofs) -> void
{
    // Each var is restricted to a fragmented value list via In, so AllEqual
    // sees multi-interval inputs and exercises the hole-elimination path.
    print(cerr, "all_equal with holes{}", proofs ? " with proofs:" : ":");
    cerr << flush;

    vector<int> dx{1, 3, 5, 7, 9};
    vector<int> dy{2, 3, 5, 6, 9};
    vector<int> dz{3, 4, 5, 8, 9};

    set<tuple<int, int, int>> expected, actual;
    build_expected(
        expected,
        [&](int x, int y, int z) -> bool {
            auto in = [](int v, const vector<int> & s) {
                for (auto u : s)
                    if (u == v) return true;
                return false;
            };
            return x == y && y == z && in(x, dx) && in(y, dy) && in(z, dz);
        },
        pair{1, 10}, pair{1, 10}, pair{1, 10});
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto x = p.create_integer_variable(1_i, 10_i);
    auto y = p.create_integer_variable(1_i, 10_i);
    auto z = p.create_integer_variable(1_i, 10_i);

    auto to_integers = [](const vector<int> & vs) {
        vector<Integer> out;
        for (auto v : vs)
            out.emplace_back(v);
        return out;
    };
    p.post(In{x, to_integers(dx)});
    p.post(In{y, to_integers(dy)});
    p.post(In{z, to_integers(dz)});
    p.post(AllEqual{vector<IntegerVariableID>{x, y, z}});

    auto proof_name = proofs ? make_optional("all_equal_test_holes") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{x, y, z});
    check_results(proof_name, expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<vector<pair<int, int>>> data = {
        {{1, 5}, {3, 8}},
        {{1, 3}, {5, 8}},
        {{1, 4}, {1, 4}},
        {{1, 5}, {2, 6}, {3, 7}},
        {{2, 4}, {2, 4}, {2, 4}},
        {{1, 6}, {2, 5}, {3, 4}, {4, 7}},
    };

    random_device rand_dev;
    mt19937 rand(rand_dev());
    auto random_run = [&](int n_vars) {
        vector<pair<int, int>> doms;
        std::uniform_int_distribution<int> lo_dist{-3, 5};
        std::uniform_int_distribution<int> width_dist{0, 5};
        for (int i = 0; i < n_vars; ++i) {
            int lo = lo_dist(rand);
            doms.emplace_back(lo, lo + width_dist(rand));
        }
        data.push_back(doms);
    };
    for (int i = 0; i < 5; ++i) random_run(2);
    for (int i = 0; i < 5; ++i) random_run(3);
    for (int i = 0; i < 3; ++i) random_run(4);

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (const auto & doms : data)
            run_test(proofs, doms);
        run_holes_test(proofs);
    }

    return EXIT_SUCCESS;
}
