#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/sort.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <algorithm>
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

namespace
{
    auto is_sorted_permutation(const vector<int> & x, const vector<int> & y) -> bool
    {
        if (x.size() != y.size())
            return false;
        for (size_t i = 0; i + 1 < y.size(); ++i)
            if (y[i] > y[i + 1])
                return false;
        auto xs = x, ys = y;
        std::sort(xs.begin(), xs.end());
        std::sort(ys.begin(), ys.end());
        return xs == ys;
    }

    auto run_sort_test(bool proofs, const vector<pair<int, int>> & x_domains, const vector<pair<int, int>> & y_domains) -> void
    {
        print(cerr, "sort x={} y={}{}", x_domains, y_domains, proofs ? " with proofs:" : ":");
        cerr << flush;

        set<tuple<vector<int>, vector<int>>> expected, actual;
        build_expected(
            expected, [](const vector<int> & x, const vector<int> & y) { return is_sorted_permutation(x, y); },
            x_domains, y_domains);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        vector<IntegerVariableID> x, y;
        for (const auto & d : x_domains)
            x.push_back(p.create_integer_variable(Integer(d.first), Integer(d.second)));
        for (const auto & d : y_domains)
            y.push_back(p.create_integer_variable(Integer(d.first), Integer(d.second)));
        p.post(Sort{x, y});

        // The Mehlhorn-Thiel propagator achieves bounds consistency on both x
        // and y (exact 1-D projections), so assert BC at every search node.
        auto proof_name = proofs ? make_optional("sort_test") : nullopt;
        solve_for_tests_checking_consistency(p, proof_name, expected, actual,
            tuple{std::make_pair(x, CheckConsistency::BC), std::make_pair(y, CheckConsistency::BC)});
        check_results(proof_name, expected, actual);
    }

    // Dup-variable case: the same handle appears twice in x. The constraint is
    // purely value-based (count multiset equality), so aliasing is handled
    // correctly -- it simply means that value occurs twice.
    auto run_sort_dup_test(bool proofs, const vector<pair<int, int>> & unique_domains,
        const vector<int> & x_positions, const vector<int> & y_positions) -> void
    {
        print(cerr, "sort dup domains={} x_pos={} y_pos={}{}", unique_domains, x_positions, y_positions,
            proofs ? " with proofs:" : ":");
        cerr << flush;

        set<tuple<vector<int>>> expected, actual;
        build_expected(
            expected, [&](const vector<int> & vals) {
                vector<int> x, y;
                for (auto i : x_positions)
                    x.push_back(vals.at(i));
                for (auto i : y_positions)
                    y.push_back(vals.at(i));
                return is_sorted_permutation(x, y);
            },
            unique_domains);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        vector<IntegerVariableID> unique_vars;
        for (const auto & d : unique_domains)
            unique_vars.push_back(p.create_integer_variable(Integer(d.first), Integer(d.second)));
        vector<IntegerVariableID> x, y;
        for (auto i : x_positions)
            x.push_back(unique_vars.at(i));
        for (auto i : y_positions)
            y.push_back(unique_vars.at(i));
        p.post(Sort{x, y});

        auto proof_name = proofs ? make_optional("sort_test_dup") : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{unique_vars});
        check_results(proof_name, expected, actual);
    }
}

auto main(int argc, char * argv[]) -> int
{
    set_seed_from_argv(argc, argv);

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;

        // all equal
        run_sort_test(proofs, {{2, 2}, {2, 2}}, {{2, 2}, {2, 2}});
        // Pairs.
        run_sort_test(proofs, {{0, 2}, {0, 2}}, {{0, 2}, {0, 2}});
        // Triples, full domains -> exercises duplicate values in the sorted output.
        run_sort_test(proofs, {{0, 2}, {0, 2}, {0, 2}}, {{0, 2}, {0, 2}, {0, 2}});
        // Asymmetric / negative domains.
        run_sort_test(proofs, {{-1, 1}, {0, 2}, {1, 3}}, {{-1, 3}, {-1, 3}, {-1, 3}});
        // Output domains narrower than inputs -> some inputs become infeasible.
        run_sort_test(proofs, {{0, 3}, {0, 3}}, {{1, 2}, {1, 2}});
        // Single element (y[0] == x[0]).
        run_sort_test(proofs, {{0, 3}}, {{0, 3}});

        // n = 4, exercises the matching/SCC on a larger instance.
        run_sort_test(proofs, {{0, 3}, {0, 3}, {0, 3}, {0, 3}}, {{0, 3}, {0, 3}, {0, 3}, {0, 3}});

        // Asymmetric x domains -> y bounds are pruned by the order statistics.
        run_sort_test(proofs, {{1, 3}, {2, 5}, {0, 2}}, {{0, 5}, {0, 5}, {0, 5}});

        // Narrow y forces the x bounds in from a wide domain (x-side pruning via
        // the reduced graph): each x must end up in [2,3] or [5,6].
        run_sort_test(proofs, {{0, 9}, {0, 9}}, {{2, 3}, {5, 6}});

        // Overlapping windows that trigger Hall-interval reasoning.
        run_sort_test(proofs, {{0, 2}, {3, 5}, {1, 4}}, {{0, 5}, {0, 5}, {0, 5}});

        // NESTED-BAND cases: narrow y-windows confine specific x's to a band of
        // positions, so the y-bound is NOT the plain order statistic -- this is
        // the windowed Hall case (Stage 4 of the proof), which the cases above
        // never exercise. Here x[1],x[2] in [1,2] can only sit at positions 1,2
        // (y[0] forces <= the low window, y[3] the high one), a tight band.
        run_sort_test(proofs, {{0, 5}, {2, 3}, {2, 3}, {0, 5}}, {{0, 1}, {2, 3}, {2, 3}, {4, 5}});
        // A 5-element version with two distinct confined groups.
        run_sort_test(proofs, {{0, 6}, {1, 2}, {1, 2}, {3, 4}, {0, 6}},
            {{0, 0}, {1, 2}, {1, 2}, {3, 4}, {5, 6}});

        // Infeasible y-windows: y[0] in [5,6] but y[1] in [0,1] can't be sorted
        // (exercises the pure-sortedness no-matching contradiction at the root).
        run_sort_test(proofs, {{0, 9}, {0, 9}}, {{5, 6}, {0, 1}});
        run_sort_test(proofs, {{0, 9}, {0, 9}, {0, 9}}, {{0, 1}, {5, 6}, {2, 3}});
        // Matching infeasibility (Hall violator on the rank line): three x's all
        // pinned to value 0 can't supply the distinct sorted values 0,1,2.
        run_sort_test(proofs, {{0, 0}, {0, 0}, {0, 0}}, {{0, 0}, {1, 1}, {2, 2}});
        // A non-trivial band: three x's confined to ranks {0,1} (values <= 2)
        // can't cover the third sorted value 3 -- the pigeonhole spans two ranks.
        run_sort_test(proofs, {{1, 2}, {1, 2}, {1, 2}}, {{1, 1}, {2, 2}, {3, 3}});

        // Aliasing within x: x = (a, a), y = (b, c).
        run_sort_dup_test(proofs, {{0, 2}, {0, 2}, {0, 2}}, {0, 0}, {1, 2});

        // NB: the large-count order-statistic case (verifying that the count
        // line stays RUP at high degree, over non-fixed x with upper bounds
        // strictly below the threshold) is NOT here -- the enumerate-and-compare
        // harness can't take wide domains. It lives as a standalone proof-only
        // probe: examples/sort_count_probe.
    }

    // Seeded randomized batch: sizes up to 5, a mix of wide y-windows (exercising
    // order-statistic / x-side bounds and infeasibility) and narrow sorted
    // windows (exercising banded Hall reasoning). Reproduce a failure with
    // --seed=N (the printed domains pin the instance down too).
    auto random_instance = [](mt19937 & r) -> pair<vector<pair<int, int>>, vector<pair<int, int>>> {
        uniform_int_distribution<int> n_dist{2, 5}, lo_dist{-1, 3}, w_dist{0, 3}, mode{0, 2}, wy_dist{0, 2};
        int n = n_dist(r);
        vector<pair<int, int>> xd;
        int gmin = 0, gmax = 0;
        for (int i = 0; i < n; ++i) {
            int l = lo_dist(r), u = l + w_dist(r);
            xd.emplace_back(l, u);
            gmin = (i == 0) ? l : std::min(gmin, l);
            gmax = (i == 0) ? u : std::max(gmax, u);
        }
        vector<pair<int, int>> yd;
        if (mode(r) == 0) {
            for (int i = 0; i < n; ++i)
                yd.emplace_back(gmin, gmax);
        }
        else {
            vector<int> ls;
            uniform_int_distribution<int> v_dist{gmin, gmax};
            for (int i = 0; i < n; ++i)
                ls.push_back(v_dist(r));
            std::sort(ls.begin(), ls.end());
            for (int i = 0; i < n; ++i)
                yd.emplace_back(ls[i], ls[i] + wy_dist(r));
        }
        return {xd, yd};
    };

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        auto seed = get_seed();
        mt19937 rng(seed ? *seed : random_device{}());
        for (int t = 0; t < 8; ++t) {
            auto [xd, yd] = random_instance(rng);
            run_sort_test(proofs, xd, yd);
        }
    }

    return EXIT_SUCCESS;
}
