#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/knapsack.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <util/enumerate.hh>

#include <cstdlib>
#include <functional>
#include <iostream>
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
using std::max;
using std::mt19937;
using std::nullopt;
using std::pair;
using std::random_device;
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

auto run_knapsack_test(bool proofs, pair<int, int> valrange, const vector<vector<int>> & coeffs, const vector<pair<int, int>> & bounds) -> void
{
    print(cerr, "knapsack {} {} {} {}", valrange, coeffs, bounds, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<vector<int>, vector<int>>> expected, actual;

    auto is_satisfying = [&](const vector<int> & taken, const vector<int> & profits) {
        vector<int> sums(coeffs.size(), 0);
        for (const auto & [x, s] : enumerate(taken))
            for (unsigned i = 0; i < coeffs.size(); ++i)
                sums[i] += coeffs[i][x] * s;

        for (unsigned i = 0; i < coeffs.size(); ++i)
            if (! (sums[i] >= bounds[i].first && sums[i] <= bounds[i].second))
                return false;

        return sums == profits;
    };
    // Enumerate only the `taken` assignments. The total/profit variables are
    // functionally determined (the constraint forces each total to equal its
    // weighted sum), so compute them rather than enumerating their ranges and
    // filtering with `sums == profits`. The latter made build_expected the
    // dominant cost on this test, since totals range up to ~1000.
    auto n_items = coeffs[0].size();
    std::vector<int> taken(n_items);
    std::function<auto(std::size_t)->void> enumerate_taken = [&](std::size_t pos) -> void {
        if (pos == n_items) {
            std::vector<int> sums(coeffs.size(), 0);
            for (std::size_t i = 0; i < coeffs.size(); ++i)
                for (std::size_t k = 0; k < n_items; ++k)
                    sums[i] += coeffs[i][k] * taken[k];
            if (is_satisfying(taken, sums))
                expected.emplace(taken, sums);
            return;
        }
        for (int v = valrange.first; v <= valrange.second; ++v) {
            taken[pos] = v;
            enumerate_taken(pos + 1);
        }
    };
    enumerate_taken(0);

    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto vs = p.create_integer_variable_vector(coeffs[0].size(), Integer(valrange.first), Integer(valrange.second));
    vector<IntegerVariableID> bs;
    for (unsigned i = 0; i < coeffs.size(); ++i)
        bs.push_back(p.create_integer_variable(Integer(bounds[i].first), Integer(bounds[i].second)));
    vector<vector<Integer>> coeffs_integers(coeffs.size());
    for (unsigned i = 0; i < coeffs.size(); ++i)
        for (const auto & w : coeffs[i])
            coeffs_integers[i].push_back(Integer(w));

    p.post(Knapsack{coeffs_integers, vs, bs});

    auto proof_name = proofs ? make_optional("knapsack_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{vs, bs});

    check_results(proof_name, expected, actual);
}

// Dup-variable test: Knapsack with a duplicated handle in `vars` (or in
// `totals`). Two vars positions sharing a handle should be equivalent
// to one position with summed coefficients; the PB encoding sums by
// coefficient in normal form. Consistency isn't checked on dup runs;
// see tmp/duplicate_var_audit.md.
auto run_dup_knapsack_test(bool proofs, const string & label,
    pair<int, int> valrange,
    const vector<pair<int, int>> & unique_var_domains,
    const vector<int> & positions,
    const vector<vector<int>> & coeffs,
    const vector<pair<int, int>> & totals_bounds) -> void
{
    print(cerr, "knapsack dup {} val={} unique_doms={} positions={} coeffs={} totals={}{}",
        label, valrange, unique_var_domains, positions, coeffs, totals_bounds,
        proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<vector<int>, vector<int>>> expected, actual;
    build_expected(
        expected, [&](const vector<int> & unique_vals, const vector<int> & profits) -> bool {
            vector<int> taken;
            for (auto pos : positions)
                taken.push_back(unique_vals.at(pos));
            vector<int> sums(coeffs.size(), 0);
            for (unsigned i = 0; i < coeffs.size(); ++i) {
                for (unsigned k = 0; k < taken.size(); ++k)
                    sums[i] += coeffs[i].at(k) * taken[k];
                if (sums[i] < totals_bounds[i].first || sums[i] > totals_bounds[i].second)
                    return false;
            }
            return sums == profits;
        },
        unique_var_domains, totals_bounds);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> unique_vars;
    for (const auto & d : unique_var_domains)
        unique_vars.push_back(p.create_integer_variable(Integer(d.first), Integer(d.second)));
    vector<IntegerVariableID> vs;
    for (auto pos : positions)
        vs.push_back(unique_vars.at(pos));
    vector<IntegerVariableID> bs;
    for (const auto & b : totals_bounds)
        bs.push_back(p.create_integer_variable(Integer(b.first), Integer(b.second)));
    vector<vector<Integer>> coeffs_i;
    for (const auto & row : coeffs) {
        coeffs_i.emplace_back();
        for (auto c : row)
            coeffs_i.back().push_back(Integer(c));
    }
    p.post(Knapsack{coeffs_i, vs, bs});

    auto proof_name = proofs ? make_optional("knapsack_test_dup_" + label) : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{unique_vars, bs});
    check_results(proof_name, expected, actual);
    (void) valrange;
}

auto main(int, char *[]) -> int
{
    vector<tuple<pair<int, int>, vector<vector<int>>, vector<pair<int, int>>>> data = {
        {{0, 1}, {{2, 3, 4}, {2, 3, 4}}, {{0, 8}, {3, 1000}}},
        {{0, 1}, {{2, 3, 4}, {2, 3, 4}}, {{3, 8}, {3, 1000}}},
        {{0, 1}, {{2, 3, 4}, {2, 3, 4}}, {{0, 8}, {3, 5}}},
        {{0, 1}, {{1, 3, 4}, {2, 0, 8}}, {{0, 8}, {3, 1000}}},
        {{0, 1}, {{2, 0, 8}, {1, 3, 4}}, {{0, 8}, {3, 1000}}},
        {{0, 1}, {{2, 0, 8}, {2, 0, 8}}, {{0, 8}, {3, 1000}}},
        {{0, 1}, {{2, 2, 2, 2, 2}, {2, 2, 2, 2, 2}}, {{0, 5}, {5, 1000}}},
        {{0, 1}, {{3, 3, 2, 3}, {2, 5, 6, 8}}, {{0, 7}, {4, 1000}}},
        {{0, 1}, {{8, 2, 4, 3}, {6, 5, 5, 6}}, {{0, 4}, {13, 1000}}},
        {{0, 1}, {{5, 4, 8, 7}, {2, 5, 1, 5}}, {{0, 12}, {5, 1000}}},
        {{0, 1}, {{8, 7, 4, 8}, {4, 3, 4, 4}}, {{0, 18}, {10, 1000}}},
        {{0, 1}, {{7, 4, 4, 7}, {1, 2, 1, 0}}, {{18, 19}, {3, 8}}},
        {{2, 4}, {{4, 1, 2, 3}, {4, 6, 3, 8}, {5, 3, 1, 6}}, {{0, 64}, {0, 48}, {0, 41}}},
        {{1, 4}, {{1, 8, 3, 1}}, {{3, 42}}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());
    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution n_coeffs_dist(1, 4), size_dist(1, 4), item_dist(0, 8), bound_dist(0, 40), delta_dist(0, 30);
        auto size = size_dist(rand);
        auto n_coeffs = n_coeffs_dist(rand);

        vector<pair<int, int>> boundses;
        for (int k = 0; k < n_coeffs; ++k) {
            auto wb = bound_dist(rand) + 20;
            boundses.emplace_back(max(0, wb - (25 + delta_dist(rand))), wb);
        }

        generate_random_data(rand, data, random_bounds(0, 2, 1, 3), vector(n_coeffs, vector(size, item_dist)), boundses);
    }

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & [valrange, coeffs, bounds] : data)
            run_knapsack_test(proofs, valrange, coeffs, bounds);

        // {x, x} — single var doubled; coefficients sum (1+2)*x = 3x and
        // (2+3)*x = 5x; totals must equal those.
        run_dup_knapsack_test(proofs, "xx", {0, 3}, {{0, 3}}, {0, 0},
            {{1, 2}, {2, 3}}, {{0, 9}, {0, 15}});

        // {x, y, x} — x's coefficient is summed at positions 0 and 2.
        run_dup_knapsack_test(proofs, "xyx", {0, 2}, {{0, 2}, {0, 2}}, {0, 1, 0},
            {{1, 2, 1}, {3, 1, 2}}, {{0, 8}, {0, 12}});
    }

    return EXIT_SUCCESS;
}
