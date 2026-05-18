#include <gcs/constraints/bin_packing.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
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
using std::nullopt;
using std::pair;
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

namespace
{
    auto run_bin_packing_capa_test(bool proofs, const vector<pair<int, int>> & item_ranges,
        const vector<int> & sizes, const vector<int> & capacities) -> void
    {
        print(cerr, "bin_packing capa {} sizes={} caps={}{}", item_ranges, sizes, capacities,
            proofs ? " with proofs:" : ":");
        cerr << flush;

        auto n = item_ranges.size();
        auto num_bins = capacities.size();

        auto is_satisfying = [&](const vector<int> & items) {
            vector<int> bin_load(num_bins, 0);
            for (size_t i = 0; i < n; ++i) {
                if (items[i] < 0 || items[i] >= static_cast<int>(num_bins))
                    return false;
                bin_load[items[i]] += sizes[i];
            }
            for (size_t b = 0; b < num_bins; ++b)
                if (bin_load[b] > capacities[b])
                    return false;
            return true;
        };

        set<vector<int>> expected, actual;
        build_expected(expected, is_satisfying, item_ranges);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        vector<IntegerVariableID> items;
        for (auto & [lo, hi] : item_ranges)
            items.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));

        vector<Integer> sizes_i, caps_i;
        for (auto s : sizes)
            sizes_i.push_back(Integer{s});
        for (auto c : capacities)
            caps_i.push_back(Integer{c});

        p.post(BinPacking{items, sizes_i, caps_i});

        auto proof_name = proofs ? make_optional("bin_packing_test") : nullopt;
        // Enumeration only — Stage 3 achieves per-bin GAC, not joint GAC
        // (joint GAC for BinPacking is NP-hard, classic subset-sum). For the
        // constant-cap form per-bin GAC is structurally identical to Stage
        // 2's floor check, so Stage 3 strengthens only the variable-load
        // form's load-pruning side. A per-bin-GAC reference checker can be
        // added later if regressions appear.
        solve_for_tests(p, proof_name, actual, tuple{items});

        check_results(proof_name, expected, actual);
    }

    auto run_bin_packing_load_test(bool proofs, const vector<pair<int, int>> & item_ranges,
        const vector<int> & sizes, const vector<pair<int, int>> & load_ranges) -> void
    {
        print(cerr, "bin_packing load {} sizes={} loads={}{}", item_ranges, sizes, load_ranges,
            proofs ? " with proofs:" : ":");
        cerr << flush;

        auto n = item_ranges.size();
        auto num_bins = load_ranges.size();

        auto is_satisfying = [&](const vector<int> & items, const vector<int> & loads) {
            vector<int> bin_load(num_bins, 0);
            for (size_t i = 0; i < n; ++i) {
                if (items[i] < 0 || items[i] >= static_cast<int>(num_bins))
                    return false;
                bin_load[items[i]] += sizes[i];
            }
            for (size_t b = 0; b < num_bins; ++b)
                if (bin_load[b] != loads[b])
                    return false;
            return true;
        };

        set<pair<vector<int>, vector<int>>> expected, actual;
        build_expected(expected, is_satisfying, item_ranges, load_ranges);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        vector<IntegerVariableID> items, loads;
        for (auto & [lo, hi] : item_ranges)
            items.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));
        for (auto & [lo, hi] : load_ranges)
            loads.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));

        vector<Integer> sizes_i;
        for (auto s : sizes)
            sizes_i.push_back(Integer{s});

        p.post(BinPacking{items, sizes_i, loads});

        auto proof_name = proofs ? make_optional("bin_packing_test") : nullopt;
        // Enumeration only; see capa runner for why per-bin GAC isn't
        // checked here.
        solve_for_tests(p, proof_name, actual, tuple{items, loads});

        check_results(proof_name, expected, actual);
    }
}

auto main(int, char *[]) -> int
{
    // Each capa case: { item_ranges, sizes, capacities }.
    vector<tuple<vector<pair<int, int>>, vector<int>, vector<int>>> capa_data = {
        // Two items, two bins, capacity covers any single item but not both.
        {{{0, 1}, {0, 1}}, {2, 2}, {3, 3}},
        // Per-bin different capacities.
        {{{0, 1}, {0, 1}, {0, 1}}, {1, 2, 2}, {3, 2}},
        // Single bin: items must all fit in it.
        {{{0, 0}, {0, 0}, {0, 0}}, {1, 1, 1}, {3}},
        // Capacity 0: only zero-size items allowed.
        {{{0, 1}, {0, 1}}, {0, 1}, {0, 5}},
        // Three bins, tight: forces a specific partition.
        {{{0, 2}, {0, 2}, {0, 2}, {0, 2}}, {2, 2, 1, 1}, {2, 2, 2}},
        // Unsatisfiable: one item too big for any bin.
        {{{0, 1}, {0, 1}}, {3, 1}, {2, 2}},
        // Restricted item domain: item 0 can only go in bin 1.
        {{{1, 1}, {0, 1}}, {2, 2}, {2, 3}},
        // Stage 2: capacity-tight prune. Items 1 + 2 together would exceed
        // capacity, so wherever item 0 (size 3) is pinned, items 1 and 2
        // must split.
        {{{0, 1}, {0, 1}, {0, 1}}, {3, 2, 1}, {3, 3}},
        // Stage 2: floor-overflow contradiction reachable by partial
        // assignment alone (two size-2 items pre-pinned to bin 0, capacity 3).
        {{{0, 0}, {0, 0}, {0, 1}}, {2, 2, 1}, {3, 3}},
    };

    // Each load case: { item_ranges, sizes, load_ranges }.
    vector<tuple<vector<pair<int, int>>, vector<int>, vector<pair<int, int>>>> load_data = {
        // Two items, two bins, loads free between 0..3.
        {{{0, 1}, {0, 1}}, {2, 1}, {{0, 3}, {0, 3}}},
        // Loads pinned to a specific shape.
        {{{0, 1}, {0, 1}, {0, 1}}, {1, 1, 1}, {{1, 1}, {2, 2}}},
        // Load upper bound prunes items.
        {{{0, 1}, {0, 1}, {0, 1}}, {2, 2, 2}, {{0, 2}, {0, 6}}},
        // Three bins.
        {{{0, 2}, {0, 2}, {0, 2}}, {1, 2, 3}, {{0, 6}, {0, 6}, {0, 6}}},
        // Size 0 items don't affect loads.
        {{{0, 1}, {0, 1}}, {0, 1}, {{0, 1}, {0, 1}}},
        // Stage 2: load floor lifts loads[b] lower bound. Item 0 is
        // pinned to bin 0, so loads[0] must reach 3.
        {{{0, 0}, {0, 1}, {0, 1}}, {3, 1, 1}, {{0, 10}, {0, 10}}},
        // Stage 2: load ceiling drops loads[b] upper bound. With only
        // two items possibly in bin 0, total possible mass in bin 0 is 4.
        {{{0, 1}, {0, 1}, {1, 1}}, {2, 2, 2}, {{0, 10}, {0, 10}}},
        // Stage 2: force-in via load lower bound. loads[0] >= 5 and the
        // only way to reach it is to include the size-3 + size-2 items.
        {{{0, 1}, {0, 1}, {0, 1}}, {3, 2, 1}, {{5, 10}, {0, 10}}},
        // Stage 2: force-out via load upper bound. loads[0] <= 2 prunes
        // the size-3 item out of bin 0.
        {{{0, 1}, {0, 1}, {0, 1}}, {3, 2, 1}, {{0, 2}, {0, 10}}},
        // Stage 3 subset-sum case strictly stronger than Stage 2: bin 0 must
        // sum to exactly 8 with item 0 (size 1) forced in. The only
        // remaining-items subset of {3,5,7} summing to 7 is {7}. Stage 2
        // sees floor=1, ceiling=16 and load=8 ∈ [1,16] with no individual
        // item making a forced contribution — no prunes. Stage 3 walks the
        // DAG and prunes items[1]!=0 and items[2]!=0 from bin 0 (no path
        // through their "in bin 0" edges hits the unique accepting w=8).
        {{{0, 0}, {0, 1}, {0, 1}, {0, 1}}, {1, 3, 5, 7}, {{8, 8}, {0, 20}}},
    };

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & [items, sizes, caps] : capa_data)
            run_bin_packing_capa_test(proofs, items, sizes, caps);
        for (auto & [items, sizes, loads] : load_data)
            run_bin_packing_load_test(proofs, items, sizes, loads);
    }

    return EXIT_SUCCESS;
}
