#include <gcs/constraints/disjunctive_2d.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <random>
#include <set>
#include <string>
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
using std::min;
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

namespace
{
    // A rectangle is "ignored" in non-strict mode iff it is zero-area.
    auto zero_area(int w, int h) -> bool
    {
        return w == 0 || h == 0;
    }

    auto run_disjunctive_2d_test(bool proofs, const string & mode, bool strict, const string & tag,
        const vector<pair<int, int>> & x_ranges, const vector<pair<int, int>> & y_ranges,
        const vector<int> & widths, const vector<int> & heights) -> void
    {
        auto n = x_ranges.size();
        print(cerr, "disjunctive2d{} {} xr={} yr={} w={} h={}{}", strict ? "_strict" : "",
            tag, x_ranges, y_ranges, widths, heights, proofs ? " with proofs:" : ":");
        cerr << flush;

        // Solution vector layout: xs (n) then ys (n).
        auto is_satisfying = [&](const vector<int> & vals) {
            for (size_t i = 0; i < n; ++i)
                for (size_t j = i + 1; j < n; ++j) {
                    if (! strict && (zero_area(widths[i], heights[i]) || zero_area(widths[j], heights[j])))
                        continue;
                    int xi = vals[i], yi = vals[n + i], xj = vals[j], yj = vals[n + j];
                    bool sep = (xi + widths[i] <= xj) || (xj + widths[j] <= xi) ||
                        (yi + heights[i] <= yj) || (yj + heights[j] <= yi);
                    if (! sep)
                        return false;
                }
            return true;
        };

        vector<pair<int, int>> all_ranges = x_ranges;
        all_ranges.insert(all_ranges.end(), y_ranges.begin(), y_ranges.end());

        set<vector<int>> expected, actual;
        build_expected(expected, is_satisfying, all_ranges);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        vector<IntegerVariableID> xs, ys, all_vars;
        for (auto & [lo, hi] : x_ranges) {
            auto v = p.create_integer_variable(Integer{lo}, Integer{hi});
            xs.push_back(v);
            all_vars.push_back(v);
        }
        for (auto & [lo, hi] : y_ranges) {
            auto v = p.create_integer_variable(Integer{lo}, Integer{hi});
            ys.push_back(v);
        }
        all_vars.insert(all_vars.end(), ys.begin(), ys.end());

        vector<Integer> widths_i, heights_i;
        for (auto w : widths)
            widths_i.push_back(Integer{w});
        for (auto h : heights)
            heights_i.push_back(Integer{h});

        p.post(Disjunctive2D{xs, ys, widths_i, heights_i, strict});

        auto proof_name = proofs ? make_optional("disjunctive_2d_test_" + mode + "_" + tag) : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{all_vars});
        check_results(proof_name, expected, actual);
    }

    // Dup-variable test: two rectangles sharing the same x handle (they can
    // still separate in y). Consistency isn't checked on dup runs.
    auto run_dup_disjunctive_2d_test(bool proofs, const string & mode, bool strict,
        const vector<pair<int, int>> & unique_x_ranges, const vector<pair<int, int>> & y_ranges,
        const vector<int> & x_positions, const vector<int> & widths, const vector<int> & heights) -> void
    {
        auto n = x_positions.size();
        print(cerr, "disjunctive2d{} dup ux={} yr={} xpos={} w={} h={}{}", strict ? "_strict" : "",
            unique_x_ranges, y_ranges, x_positions, widths, heights, proofs ? " with proofs:" : ":");
        cerr << flush;

        // Enumerated layout: unique xs (m) then ys (n).
        auto m = unique_x_ranges.size();
        auto is_satisfying = [&](const vector<int> & vals) {
            for (size_t i = 0; i < n; ++i)
                for (size_t j = i + 1; j < n; ++j) {
                    if (! strict && (zero_area(widths[i], heights[i]) || zero_area(widths[j], heights[j])))
                        continue;
                    int xi = vals[x_positions[i]], xj = vals[x_positions[j]];
                    int yi = vals[m + i], yj = vals[m + j];
                    bool sep = (xi + widths[i] <= xj) || (xj + widths[j] <= xi) ||
                        (yi + heights[i] <= yj) || (yj + heights[j] <= yi);
                    if (! sep)
                        return false;
                }
            return true;
        };

        vector<pair<int, int>> all_ranges = unique_x_ranges;
        all_ranges.insert(all_ranges.end(), y_ranges.begin(), y_ranges.end());

        set<vector<int>> expected, actual;
        build_expected(expected, is_satisfying, all_ranges);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        vector<IntegerVariableID> unique_xs, ys, all_vars;
        for (auto & [lo, hi] : unique_x_ranges) {
            auto v = p.create_integer_variable(Integer{lo}, Integer{hi});
            unique_xs.push_back(v);
            all_vars.push_back(v);
        }
        for (auto & [lo, hi] : y_ranges) {
            auto v = p.create_integer_variable(Integer{lo}, Integer{hi});
            ys.push_back(v);
        }
        all_vars.insert(all_vars.end(), ys.begin(), ys.end());

        vector<IntegerVariableID> xs;
        for (auto pos : x_positions)
            xs.push_back(unique_xs.at(pos));

        vector<Integer> widths_i, heights_i;
        for (auto w : widths)
            widths_i.push_back(Integer{w});
        for (auto h : heights)
            heights_i.push_back(Integer{h});

        p.post(Disjunctive2D{xs, ys, widths_i, heights_i, strict});

        auto proof_name = proofs ? make_optional("disjunctive_2d_test_" + mode + "_dup") : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{all_vars});
        check_results(proof_name, expected, actual);
    }
}

auto main(int argc, char * argv[]) -> int
{
    if (argc != 2)
        throw UnimplementedException{};

    string mode{argv[1]};
    bool strict;
    if (mode == "strict")
        strict = true;
    else if (mode == "nonstrict")
        strict = false;
    else
        throw UnimplementedException{};

    // Each test: { x_ranges, y_ranges, widths, heights }
    vector<tuple<vector<pair<int, int>>, vector<pair<int, int>>, vector<int>, vector<int>>> data = {
        // Two unit squares on a small grid.
        {{{0, 2}, {0, 2}}, {{0, 2}, {0, 2}}, {1, 1}, {1, 1}},
        // Two 2x2 squares: must separate in some direction.
        {{{0, 3}, {0, 3}}, {{0, 3}, {0, 3}}, {2, 2}, {2, 2}},
        // Asymmetric rectangles (wide vs tall).
        {{{0, 3}, {0, 3}}, {{0, 3}, {0, 3}}, {2, 1}, {1, 2}},
        // Three unit squares in a 2x2 grid: tight.
        {{{0, 1}, {0, 1}, {0, 1}}, {{0, 1}, {0, 1}, {0, 1}}, {1, 1, 1}, {1, 1, 1}},
        // Trivially unsat: two overlapping squares pinned at the origin.
        {{{0, 0}, {0, 0}}, {{0, 0}, {0, 0}}, {2, 2}, {2, 2}},
        // A zero-area (zero-width) rectangle alongside a real one.
        {{{0, 2}, {0, 2}}, {{0, 2}, {0, 2}}, {0, 2}, {2, 2}},
        // Wider value ranges so we don't hit small-value coincidences.
        {{{0, 4}, {0, 4}}, {{0, 4}, {0, 4}}, {3, 2}, {2, 3}},
    };

    random_device rand_dev;
    mt19937 rand(rand_dev());

    auto random_instance = [&](int n, int max_pos, int max_size)
        -> tuple<vector<pair<int, int>>, vector<pair<int, int>>, vector<int>, vector<int>> {
        uniform_int_distribution<> lo_dist(0, max_pos), span_dist(0, max_pos),
            size_dist(0, max_size);
        vector<pair<int, int>> xr, yr;
        vector<int> w, h;
        for (int i = 0; i < n; ++i) {
            auto xlo = lo_dist(rand), xsp = span_dist(rand);
            xr.emplace_back(xlo, min(xlo + xsp, max_pos));
            auto ylo = lo_dist(rand), ysp = span_dist(rand);
            yr.emplace_back(ylo, min(ylo + ysp, max_pos));
            w.push_back(size_dist(rand));
            h.push_back(size_dist(rand));
        }
        return {xr, yr, w, h};
    };

    // 25 small random cases (n=2 or 3, narrow grids).
    for (int k = 0; k < 25; ++k) {
        uniform_int_distribution<> n_dist(2, 3);
        data.push_back(random_instance(n_dist(rand), 2, 2));
    }
    // 10 medium random cases (n=3, wider grids).
    for (int k = 0; k < 10; ++k)
        data.push_back(random_instance(3, 3, 3));

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        int idx = 0;
        for (auto & [xr, yr, w, h] : data)
            run_disjunctive_2d_test(proofs, mode, strict, "d" + std::to_string(idx++), xr, yr, w, h);

        // Two rectangles share an x handle: they may still separate in y.
        run_dup_disjunctive_2d_test(proofs, mode, strict, {{0, 2}}, {{0, 2}, {0, 2}},
            {0, 0}, {2, 2}, {1, 1});
    }

    return EXIT_SUCCESS;
}
