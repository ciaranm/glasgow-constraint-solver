#include <gcs/constraints/bin_packing/bin_packing.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <optional>
#include <set>
#include <tuple>
#include <utility>
#include <variant>
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
using std::variant;
using std::vector;
using std::visit;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
using std::print;
using std::println;
#else
using fmt::format;
using fmt::print;
using fmt::println;
#endif

using namespace gcs;
using namespace gcs::test_innards;

namespace
{
    auto run_bin_packing_capa_test(bool proofs, bool upfront, bool cardinality, const ViewWrapConfig & view_cfg,
        const vector<pair<int, int>> & item_ranges, const vector<int> & sizes, const vector<int> & capacities) -> unsigned long long
    {
        print(cerr, "bin_packing capa [{}] {} sizes={} caps={}{}{}{}", view_wrap_config_label(view_cfg), item_ranges, sizes, capacities,
            upfront ? " upfront" : "", cardinality ? " cardinality" : "", proofs ? " with proofs:" : ":");
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
        // The items are what every MiniZinc model now hands over as views: the
        // redefinition passes the bin offset and fzn_glasgow applies it with
        // operator+, so BinPacking sees `bin[i] + -offset` rather than a variable
        // of its own. The wrap lands back on the requested visible domain, so the
        // solution set is unchanged and only the view plumbing differs.
        auto wraps = wraps_for_positions(view_cfg, static_cast<int>(item_ranges.size()));
        vector<IntegerVariableID> items;
        for (size_t i = 0; i < item_ranges.size(); ++i)
            items.push_back(create_integer_variable_or_constant_with_view(p, item_ranges.at(i), wraps.at(i)));

        vector<Integer> sizes_i, caps_i;
        for (auto s : sizes)
            sizes_i.push_back(Integer{s});
        for (auto c : capacities)
            caps_i.push_back(Integer{c});

        p.post(BinPacking{items, sizes_i, caps_i} //
                .with_proof_strategy(
                    upfront ? BinPackingProofStrategy{proof_strategy::Upfront{}} : BinPackingProofStrategy{proof_strategy::PerCall{}})
                .with_cardinality_reasoning(
                    cardinality ? BinPackingCardinality{bin_packing::Shaw{}} : BinPackingCardinality{bin_packing::NoCardinality{}}));

        auto proof_name = proofs ? make_optional("bin_packing_test_" + view_wrap_config_label(view_cfg)) : nullopt;
        // Enumeration only — Stage 3 achieves per-bin GAC, not joint GAC
        // (joint GAC for BinPacking is NP-hard, classic subset-sum). For the
        // constant-cap form per-bin GAC is structurally identical to Stage
        // 2's floor check, so Stage 3 strengthens only the variable-load
        // form's load-pruning side. A per-bin-GAC reference checker can be
        // added later if regressions appear.
        solve_for_tests(p, proof_name, actual, tuple{items});
        auto recursions = last_run_recursions();

        check_results(proof_name, expected, actual);
        return recursions;
    }

    // load_holes, if given, has for each bin the values its load's range starts
    // without.
    auto run_bin_packing_load_test(bool proofs, bool upfront, bool cardinality, const ViewWrapConfig & view_cfg,
        const vector<pair<int, int>> & item_ranges, const vector<int> & sizes, const vector<pair<int, int>> & load_ranges,
        const vector<vector<int>> & load_holes = {}) -> unsigned long long
    {
        print(cerr, "bin_packing load [{}] {} sizes={} loads={}", view_wrap_config_label(view_cfg), item_ranges, sizes, load_ranges);
        if (! load_holes.empty())
            print(cerr, " without {}", load_holes);
        print(cerr, "{}{}{}", upfront ? " upfront" : "", cardinality ? " cardinality" : "", proofs ? " with proofs:" : ":");
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
                if (bin_load[b] != loads[b] || (b < load_holes.size() && std::ranges::find(load_holes[b], loads[b]) != load_holes[b].end()))
                    return false;
            return true;
        };

        set<pair<vector<int>, vector<int>>> expected, actual;
        build_expected(expected, is_satisfying, item_ranges, load_ranges);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        // Only the items are wrapped; see the capa runner. glasgow_bin_packing_load
        // shifts the bins alone, because the load array is indexed by bin rather
        // than valued in bins, so loads stay plain variables on the MiniZinc path.
        auto wraps = wraps_for_positions(view_cfg, static_cast<int>(item_ranges.size()));
        vector<IntegerVariableID> items, loads;
        for (size_t i = 0; i < item_ranges.size(); ++i)
            items.push_back(create_integer_variable_or_constant_with_view(p, item_ranges.at(i), wraps.at(i)));
        for (size_t b = 0; b < load_ranges.size(); ++b) {
            vector<Integer> domain;
            for (auto v = load_ranges[b].first; v <= load_ranges[b].second; ++v)
                if (b >= load_holes.size() || std::ranges::find(load_holes[b], v) == load_holes[b].end())
                    domain.push_back(Integer{v});
            loads.push_back(p.create_integer_variable(domain));
        }

        vector<Integer> sizes_i;
        for (auto s : sizes)
            sizes_i.push_back(Integer{s});

        p.post(BinPacking{items, sizes_i, loads} //
                .with_proof_strategy(
                    upfront ? BinPackingProofStrategy{proof_strategy::Upfront{}} : BinPackingProofStrategy{proof_strategy::PerCall{}})
                .with_cardinality_reasoning(
                    cardinality ? BinPackingCardinality{bin_packing::Shaw{}} : BinPackingCardinality{bin_packing::NoCardinality{}}));

        auto proof_name = proofs ? make_optional("bin_packing_test_" + view_wrap_config_label(view_cfg)) : nullopt;
        // Enumeration only; see capa runner for why per-bin GAC isn't
        // checked here.
        solve_for_tests(p, proof_name, actual, tuple{items, loads});
        auto recursions = last_run_recursions();

        check_results(proof_name, expected, actual);
        return recursions;
    }

    // The proof strategy is meant to change only the proof, so the two have to
    // draw the same inferences, and so search the same tree. Until issue #995
    // the per-call Stage 3 sweep read no load and pruned nothing, and nothing
    // here noticed, because the runners above only check the solutions.
    auto check_strategies_agree(unsigned long long per_call, unsigned long long upfront) -> void
    {
        if (per_call != upfront) {
            println(cerr, "FAILED: the proof strategies searched different trees ({} recursions per-call, {} upfront)", per_call, upfront);
            exit(EXIT_FAILURE);
        }
    }

    // A load operand need not be a plain variable: the class takes
    // vector<IntegerVariableID>, so the C++ API can hand it a view or a
    // constant. Stage 4 reads each bin's ceiling out of a `pol`, which it
    // cites only for a plain variable, so it has to step around such a bin
    // rather than throw --- and the answer has to come out the same whether or
    // not proofs are being written. Stage 3's upfront proof cites the load's
    // bound in a `pol` too, and used to throw for a constant or a view load
    // (issue #1195), so `upfront` runs the same model under that strategy,
    // with or without Shaw.
    auto run_stage4_degenerate_load_test(bool proofs, const vector<pair<int, int>> & item_ranges, const vector<int> & sizes,
        const vector<pair<int, int>> & load_ranges, size_t view_load, std::optional<size_t> constant_load, int constant_value, bool shaw = true,
        bool upfront = false, bool negated_view = false) -> void
    {
        print(cerr, "bin_packing stage4 degenerate loads {} sizes={} loads={} {}view@{}{}{}{}{}", item_ranges, sizes, load_ranges,
            negated_view ? "negated " : "", view_load, constant_load ? " constant@" + std::to_string(*constant_load) : "", shaw ? "" : " no-shaw",
            upfront ? " upfront" : "", proofs ? " with proofs:" : ":");
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
        for (size_t i = 0; i < item_ranges.size(); ++i)
            items.push_back(p.create_integer_variable(Integer{item_ranges[i].first}, Integer{item_ranges[i].second}));
        for (size_t b = 0; b < num_bins; ++b) {
            auto & [lo, hi] = load_ranges[b];
            if (constant_load && b == *constant_load)
                loads.push_back(ConstantIntegerVariableID{Integer{constant_value}});
            else if (b == view_load && negated_view)
                loads.push_back(-p.create_integer_variable(Integer{3 - hi}, Integer{3 - lo}) + 3_i);
            else if (b == view_load)
                loads.push_back(p.create_integer_variable(Integer{lo - 3}, Integer{hi - 3}) + 3_i);
            else
                loads.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));
        }

        vector<Integer> sizes_i;
        for (auto sz : sizes)
            sizes_i.push_back(Integer{sz});

        BinPacking bin_packing{items, sizes_i, loads};
        if (shaw)
            bin_packing.with_cardinality_reasoning(bin_packing::Shaw{});
        if (upfront)
            bin_packing.with_proof_strategy(proof_strategy::Upfront{});
        p.post(bin_packing);

        auto proof_name = proofs ? make_optional<std::string>("bin_packing_stage4_degen_test") : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{items, loads});

        check_results(proof_name, expected, actual);
    }

    // A constant item (issue #1192). The class takes vector<IntegerVariableID>,
    // so the C++ API can pin an item with a constant, and Stage 4 counts every
    // pinned item of positive size. Its final pol used to ask the proof tracker
    // for the item's at-least-one row, which a constant does not have, so with
    // proofs on the solve aborted, losing solutions on a satisfiable model. A
    // constant has no literal in any bin's row for that row to cancel: the OPB
    // folds it into its bin's right-hand side. With `load_form`, each bin gets a
    // load variable over 0..capacity in place of the constant capacity.
    // An item that is the same view, y + 2, as the load of a bin after bin 0.
    // The view gets its own bit vector at the first row naming it as an
    // integer term, which used to be that bin's row, so the rows before it
    // spelled the item's eq atoms through y and everything after spelled them
    // over the view's vector, and the pols over the earlier rows did not
    // cancel. Both proof strategies were affected; the upfront one reaches it
    // only now that a view load no longer throws (issue #1195).
    auto run_item_view_load_test(bool proofs, bool upfront, bool shaw, const vector<pair<int, int>> & item_ranges, pair<int, int> view_range,
        const vector<int> & sizes, size_t view_bin, const vector<int> & load_uppers) -> void
    {
        print(cerr, "bin_packing item view as load items={} view={} sizes={} view_bin={} load_uppers={}{}{}{}", item_ranges, view_range, sizes,
            view_bin, load_uppers, upfront ? " upfront" : "", shaw ? " shaw" : "", proofs ? " with proofs:" : ":");
        cerr << flush;

        auto num_bins = load_uppers.size();
        // The plain variables, in order: the items but the last, then y + 2's
        // value, then every load but the view one.
        vector<pair<int, int>> ranges = item_ranges;
        ranges.push_back(view_range);
        for (size_t b = 0; b < num_bins; ++b)
            if (b != view_bin)
                ranges.emplace_back(0, load_uppers[b]);

        auto is_satisfying = [&](const vector<int> & vals) {
            vector<int> load(num_bins, 0);
            for (size_t i = 0; i <= item_ranges.size(); ++i)
                load[vals[i]] += sizes[i];
            size_t next = item_ranges.size() + 1;
            for (size_t b = 0; b < num_bins; ++b)
                if (load[b] != (b == view_bin ? vals[item_ranges.size()] : vals[next++]))
                    return false;
            return true;
        };

        set<tuple<vector<int>>> expected, actual;
        build_expected(expected, is_satisfying, ranges);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        vector<IntegerVariableID> plain, items, loads;
        for (auto & [lo, hi] : item_ranges) {
            plain.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));
            items.push_back(plain.back());
        }
        auto y = p.create_integer_variable(Integer{view_range.first - 2}, Integer{view_range.second - 2});
        auto view = y + 2_i;
        items.push_back(view);
        plain.push_back(view);
        for (size_t b = 0; b < num_bins; ++b) {
            if (b == view_bin)
                loads.push_back(view);
            else {
                plain.push_back(p.create_integer_variable(0_i, Integer{load_uppers[b]}));
                loads.push_back(plain.back());
            }
        }

        vector<Integer> sizes_i;
        for (auto sz : sizes)
            sizes_i.push_back(Integer{sz});
        BinPacking bin_packing{items, sizes_i, loads};
        if (shaw)
            bin_packing.with_cardinality_reasoning(bin_packing::Shaw{});
        if (upfront)
            bin_packing.with_proof_strategy(proof_strategy::Upfront{});
        p.post(bin_packing);

        auto proof_name = proofs ? make_optional<std::string>("bin_packing_item_view_load_test") : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{plain});
        check_results(proof_name, expected, actual);
    }

    auto run_stage4_constant_item_test(bool proofs, bool bounds_only, bool load_form, const vector<variant<int, pair<int, int>>> & item_specs,
        const vector<int> & sizes, const vector<int> & capacities) -> void
    {
        print(cerr, "bin_packing stage4 constant items {} sizes={} {}={}{}{}", item_specs, sizes, load_form ? "load ceilings" : "caps", capacities,
            bounds_only ? " bc" : "", proofs ? " with proofs:" : ":");
        cerr << flush;

        auto n = item_specs.size();
        auto num_bins = capacities.size();

        auto loads_of = [&](const vector<int> & items) -> std::optional<vector<int>> {
            vector<int> bin_load(num_bins, 0);
            for (size_t i = 0; i < n; ++i) {
                if (items[i] < 0 || items[i] >= static_cast<int>(num_bins))
                    return nullopt;
                bin_load[items[i]] += sizes[i];
            }
            for (size_t b = 0; b < num_bins; ++b)
                if (bin_load[b] > capacities[b])
                    return nullopt;
            return bin_load;
        };

        // A load variable is fixed by its items, so the load form's solutions
        // are the capacity form's with the loads appended.
        set<pair<vector<int>, vector<int>>> expected, actual;
        set<vector<int>> item_solutions;
        build_expected(item_solutions, [&](const vector<int> & items) { return loads_of(items).has_value(); }, item_specs);
        for (const auto & items : item_solutions)
            expected.emplace(items, load_form ? *loads_of(items) : vector<int>{});
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        vector<IntegerVariableID> items, loads;
        for (const auto & spec : item_specs)
            items.push_back(visit([&](const auto & x) { return create_integer_variable_or_constant(p, x); }, spec));

        vector<Integer> sizes_i, caps_i;
        for (auto sz : sizes)
            sizes_i.push_back(Integer{sz});
        for (auto c : capacities) {
            caps_i.push_back(Integer{c});
            if (load_form)
                loads.push_back(p.create_integer_variable(0_i, Integer{c}));
        }

        auto bin_packing = load_form ? BinPacking{items, sizes_i, loads} : BinPacking{items, sizes_i, caps_i};
        bin_packing.with_cardinality_reasoning(bin_packing::Shaw{});
        if (bounds_only)
            bin_packing.with_consistency(consistency::BC{});
        p.post(bin_packing);

        auto proof_name = proofs ? make_optional<std::string>("bin_packing_stage4_constant_test") : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{items, loads});

        check_results(proof_name, expected, actual);
    }

    // Stage 4 has to be shown to do something, not just to stay sound: the
    // fixtures above would pass with the pass deleted. This is the pigeonhole
    // the per-bin passes provably cannot see --- n items each more than half a
    // bin, so a bin holds at most one, and fewer bins than items. No single
    // bin's capacity row is violated and no single bin's DAG loses an edge, so
    // Stages 2 and 3 have to branch their way to the contradiction, while
    // Stage 4 refutes it where it stands.
    auto run_stage4_pigeonhole_test(bool proofs, const ViewWrapConfig & view_cfg, size_t num_items, int size, const vector<int> & capacities) -> void
    {
        // A wide bin range is here to make the at-least-one rows come back as an
        // interval cover; printing a hundred zeroes to say so helps nobody.
        vector<int> shown_caps(capacities.begin(), capacities.begin() + std::min<size_t>(capacities.size(), 6));
        print(cerr, "bin_packing stage4 pigeonhole [{}] {} items of size {} caps={}{}{}", view_wrap_config_label(view_cfg), num_items, size,
            shown_caps, capacities.size() > 6 ? " +" + std::to_string(capacities.size() - 6) + " more bins" : "", proofs ? " with proofs:" : ":");
        cerr << flush;

        vector<Integer> sizes_i, caps_i;
        for (size_t i = 0; i < num_items; ++i)
            sizes_i.push_back(Integer{size});
        for (auto c : capacities)
            caps_i.push_back(Integer{c});

        auto solve_one = [&](bool cardinality, bool bounds_only, const std::optional<std::string> & proof_name) -> unsigned long long {
            Problem p;
            auto wraps = wraps_for_positions(view_cfg, static_cast<int>(num_items));
            vector<IntegerVariableID> items;
            for (size_t i = 0; i < num_items; ++i)
                items.push_back(
                    create_integer_variable_or_constant_with_view(p, pair<int, int>{0, static_cast<int>(capacities.size()) - 1}, wraps.at(i)));

            p.post(BinPacking{items, sizes_i, caps_i} //
                    .with_consistency(bounds_only ? BinPackingConsistency{consistency::BC{}} : BinPackingConsistency{consistency::GAC{}})
                    .with_cardinality_reasoning(
                        cardinality ? BinPackingCardinality{bin_packing::Shaw{}} : BinPackingCardinality{bin_packing::NoCardinality{}}));

            set<vector<int>> actual;
            solve_for_tests(p, proof_name, actual, tuple{items});
            if (! actual.empty()) {
                println(cerr, " FAILED: expected no solutions, got {}", actual.size());
                exit(EXIT_FAILURE);
            }
            if (proof_name)
                verify_proof_and_clean_up(*proof_name);
            return last_run_recursions();
        };

        // Same seed either side (establish_and_announce_seed pins it for the
        // whole run), so the two searches differ only in what the propagator
        // knows --- see dev_docs/benchmarking.md on why an unpinned comparison
        // measures the seed instead.
        auto without = solve_one(false, false, nullopt);
        auto with = solve_one(true, false, proofs ? make_optional("bin_packing_stage4_test_" + view_wrap_config_label(view_cfg)) : nullopt);
        // Stage 4 needs no DAG, so it has to work under consistency::BC too --- a
        // configuration where the bridge exists to carry the OPB line numbers and
        // holds no DAGs at all.
        auto with_bc = solve_one(true, true, proofs ? make_optional("bin_packing_stage4_bc_test_" + view_wrap_config_label(view_cfg)) : nullopt);
        println(cerr, " {} recursions without cardinality, {} with, {} with under BC", without, with, with_bc);

        if (with >= without || with_bc >= without) {
            println(cerr, "FAILED: Stage 4 did not cut the search ({} with, {} under BC, {} without)", with, with_bc, without);
            exit(EXIT_FAILURE);
        }
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);
    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);
    // Matches add_view_tests(bin_packing_constraint bin_packing_test 4).
    constexpr int n_positions = 4;

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
        // Stage 4 (#209): the worked example one bin wider. Bins 1 and 2 take
        // one size-2 item each and bin 0 takes the third plus the size-1 item,
        // so items[0] is pinned to bin 0 --- a cross-bin prune, with every
        // individual bin still perfectly happy to take item 0.
        {{{0, 2}, {0, 2}, {0, 2}, {0, 2}}, {1, 2, 2, 2}, {3, 2, 2}},
        // Stage 4: pure pigeonhole. Three items over half a bin each, two
        // bins; no capacity row is violated and no per-bin DAG loses an edge,
        // but there are more items than bins that can hold one.
        {{{0, 1}, {0, 1}, {0, 1}}, {7, 7, 7}, {10, 10}},
        // Stage 4: a bin with room to spare must not be allowed to pay for
        // another bin's overflow. Items 0-2 pigeonhole into bins 0 and 1, while
        // bin 2 holds one unit item and 99 units of slack. The bound needs bin
        // 2 to contribute zero; letting it contribute its own (very negative)
        // rounded capacity would sink the sum, so this is the fixture that
        // makes the max(0, R_b) clamp load-bearing rather than merely stronger.
        {{{0, 1}, {0, 1}, {0, 1}, {2, 2}}, {7, 7, 7, 1}, {10, 10, 100}},
        // Stage 4: pigeonhole with the rounding doing the work. Bins hold one
        // size-3 item each (3 + 3 > 5), so three of them do not fit in two
        // bins --- but the energy bound alone (9 <= 10) says nothing.
        {{{0, 1}, {0, 1}, {0, 1}}, {3, 3, 3}, {5, 5}},
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
        // Issue #995: only {2, 3} makes 5, so the size-4 item goes in bin 1,
        // and bin 1's load is 4. Unit propagation on the bin's equation alone
        // is enough to see it.
        {{{0, 1}, {0, 1}, {0, 1}}, {2, 3, 4}, {{5, 5}, {0, 9}}},
        // Issue #995: the size-1 item cannot be in bin 0, because what else
        // goes there is even. Unit propagation on the equation does not see
        // that, so the prune needs the per-call proof's forward chain.
        {{{0, 1}, {0, 1}, {0, 1}, {0, 1}, {0, 1}}, {1, 2, 2, 2, 2}, {{4, 4}, {0, 9}}},
        // The same with the size-1 item last, so the prune is at the bottom of
        // the DAG rather than the top. At the top, the state after one item is
        // that item's literal, which unit propagation reads off directly; at
        // the bottom it has to be reached through the chains.
        {{{0, 1}, {0, 1}, {0, 1}, {0, 1}, {0, 1}}, {2, 2, 2, 2, 1}, {{4, 4}, {0, 9}}},
        // Stage 3 cuts each load to multiples of 3, and the search then
        // branches on the loads, so a terminal's load can fall in a hole.
        {{{0, 1}, {0, 1}, {0, 1}}, {3, 3, 3}, {{0, 9}, {0, 9}}},
        // Stage 4 in the variable-load form: the same cross-bin prune as the
        // capa worked example, with the capacities arriving as load upper
        // bounds instead of constants (so the per-bin rows are read under a
        // bound literal that has to reach the reason).
        {{{0, 1}, {0, 1}, {0, 1}}, {1, 2, 2}, {{0, 3}, {0, 2}}},
        // Stage 4: pigeonhole against load upper bounds.
        {{{0, 1}, {0, 1}, {0, 1}}, {3, 3, 3}, {{0, 5}, {0, 5}}},
    };

    // Each load case with holes: { item_ranges, sizes, load_ranges, the values
    // each load's range starts without }.
    vector<tuple<vector<pair<int, int>>, vector<int>, vector<pair<int, int>>, vector<vector<int>>>> load_hole_data = {
        {{{0, 1}, {0, 1}, {0, 1}}, {1, 2, 2}, {{0, 4}, {0, 5}}, {{1, 3}, {}}},
        {{{0, 1}, {0, 1}}, {2, 2}, {{1, 4}, {0, 4}}, {{2}, {}}},
        {{{0, 1}, {0, 1}}, {2, 3}, {{0, 5}, {0, 5}}, {{2, 3}, {}}},
        {{{0, 1}, {0, 1}, {0, 1}}, {1, 4, 3}, {{0, 5}, {0, 8}}, {{2, 3, 4}, {}}},
    };

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        // Both proof strategies on every case, with and without proofs, and
        // their search trees compared (see check_strategies_agree). The
        // cardinality pass is a strength choice rather than a proof one, so it
        // is exercised on both. It is run against the upfront Stage 3 strategy
        // as well as the default: the two write into the same proof, and
        // nothing but running them together checks that they agree about what
        // the per-bin OPB rows say.
        for (bool cardinality : {false, true}) {
            for (auto & [items, sizes, caps] : capa_data)
                check_strategies_agree(run_bin_packing_capa_test(proofs, false, cardinality, view_cfg, items, sizes, caps),
                    run_bin_packing_capa_test(proofs, true, cardinality, view_cfg, items, sizes, caps));
            for (auto & [items, sizes, loads] : load_data)
                check_strategies_agree(run_bin_packing_load_test(proofs, false, cardinality, view_cfg, items, sizes, loads),
                    run_bin_packing_load_test(proofs, true, cardinality, view_cfg, items, sizes, loads));
        }

        // Loads that start with holes on terminals the DAG can reach, inside
        // their bounds, so that the per-call proof has to rule those terminals
        // out through the holes rather than a bound. One of each inference:
        // a prune (an odd load is impossible), a bound cut, and a gap cut
        // whose gap contains reachable holes; then a prune whose item can only
        // reach holes (3 or 4) or loads over the bound (7 or 8), which Stage 2
        // cannot see either. The search can make holes like these by branching
        // on a load, but only on some seeds.
        for (auto & [items, sizes, loads, holes] : load_hole_data)
            check_strategies_agree(run_bin_packing_load_test(proofs, false, false, view_cfg, items, sizes, loads, holes),
                run_bin_packing_load_test(proofs, true, false, view_cfg, items, sizes, loads, holes));

        // Seven items each needing more than half of a bin, four bins.
        run_stage4_pigeonhole_test(proofs, view_cfg, 7, 7, {10, 10, 10, 10});

        // The same refutation over a bin range wide enough that the
        // at-least-one rows come back as an interval cover rather than one term
        // per value: two unit places for three unit items, and a hundred and
        // three dead bins whose runs the reason has to rule out.
        {
            vector<int> wide_caps{1, 1};
            wide_caps.resize(105, 0);
            run_stage4_pigeonhole_test(proofs, view_cfg, 3, 1, wide_caps);
        }

        // The cross-bin prune of the worked example, with bin 1's load arriving
        // as a view and (second case) bin 0's as a constant. These build their
        // own view and never read view_cfg, so every view lane would repeat
        // the same work under the same proof name, racing the others under a
        // parallel ctest (issue #961). Run them in the bare lane only.
        if (view_wrap_config_is_effectively_bare(view_cfg, n_positions)) {
            run_stage4_degenerate_load_test(proofs, {{0, 1}, {0, 1}, {0, 1}}, {1, 2, 2}, {{0, 3}, {0, 2}}, 1, nullopt, 0);
            run_stage4_degenerate_load_test(proofs, {{0, 1}, {0, 1}, {0, 1}}, {1, 2, 2}, {{0, 3}, {0, 2}}, 1, make_optional<size_t>(0), 3);

            // The same loads under the upfront proof strategy, with and without
            // Shaw, and with the view negated (issue #1195). The last two are
            // close to the issue's instances, with item 0 pinned to bin 0: bin
            // 0's load is a constant 3 (and bin 1's a view), then a view taking
            // the values 1 to 3 (and bin 1's load plain).
            for (bool shaw : {false, true}) {
                run_stage4_degenerate_load_test(proofs, {{0, 1}, {0, 1}, {0, 1}}, {1, 2, 2}, {{0, 3}, {0, 2}}, 1, nullopt, 0, shaw, true);
                run_stage4_degenerate_load_test(proofs, {{0, 1}, {0, 1}, {0, 1}}, {1, 2, 2}, {{0, 3}, {0, 2}}, 1, nullopt, 0, shaw, true, true);
                run_stage4_degenerate_load_test(
                    proofs, {{0, 1}, {0, 1}, {0, 1}}, {1, 2, 2}, {{0, 3}, {0, 2}}, 1, make_optional<size_t>(0), 3, shaw, true);
            }
            run_stage4_degenerate_load_test(
                proofs, {{0, 0}, {0, 1}, {0, 1}}, {1, 2, 2}, {{3, 3}, {0, 4}}, 1, make_optional<size_t>(0), 3, false, true);
            run_stage4_degenerate_load_test(proofs, {{0, 0}, {0, 1}, {0, 1}}, {1, 2, 2}, {{1, 3}, {0, 4}}, 0, nullopt, 0, false, true);

            // An item that is the same view as a later bin's load, under each
            // strategy: shapes a random sweep found rejected (issue #1195).
            run_item_view_load_test(proofs, true, false, {{1, 2}, {0, 2}}, {1, 2}, {2, 2, 2}, 2, {3, 6, 2});
            run_item_view_load_test(proofs, false, true, {{0, 3}, {1, 3}}, {0, 2}, {1, 2, 3}, 3, {2, 3, 3, 4});

            // Constant items (issue #1192). The first five are shapes a random
            // sweep found aborting with proofs: one with two of its four
            // solutions reported before the abort, three whose lone solution was
            // lost, and an unsatisfiable one that aborted instead. The next two
            // are the first of them under BC, and in the variable-load form,
            // both of which aborted too. The last is a control: a zero-size
            // constant beside a rounding pigeonhole, which Stage 4 never counts,
            // so it passed before the fix as well.
            run_stage4_constant_item_test(proofs, false, false, {2, pair{0, 2}, pair{0, 2}, pair{0, 2}}, {2, 1, 3, 4}, {4, 4, 3});
            run_stage4_constant_item_test(proofs, false, false, {pair{0, 1}, pair{0, 1}, 0}, {3, 4, 3}, {7, 3});
            run_stage4_constant_item_test(proofs, false, false, {pair{0, 1}, pair{0, 1}, pair{0, 1}, 0}, {2, 3, 4, 3}, {6, 6});
            run_stage4_constant_item_test(proofs, false, false, {1, pair{0, 1}, pair{0, 1}}, {2, 2, 4}, {5, 4});
            run_stage4_constant_item_test(proofs, false, false, {1, pair{0, 2}, pair{0, 2}}, {3, 4, 4}, {7, 4, 3});
            run_stage4_constant_item_test(proofs, true, false, {2, pair{0, 2}, pair{0, 2}, pair{0, 2}}, {2, 1, 3, 4}, {4, 4, 3});
            run_stage4_constant_item_test(proofs, false, true, {2, pair{0, 2}, pair{0, 2}, pair{0, 2}}, {2, 1, 3, 4}, {4, 4, 3});
            run_stage4_constant_item_test(proofs, false, false, {pair{0, 1}, pair{0, 1}, pair{0, 1}, 1}, {3, 3, 3, 0}, {5, 5});
        }
    }

    return EXIT_SUCCESS;
}
