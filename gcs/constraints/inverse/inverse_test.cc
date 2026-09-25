#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/inverse.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <util/enumerate.hh>

#include <cstddef>
#include <cstdlib>
#include <iostream>
#include <optional>
#include <random>
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
using std::cmp_not_equal;
using std::flush;
using std::get;
using std::get_if;
using std::make_optional;
using std::mt19937;
using std::nullopt;
using std::pair;
using std::set;
using std::string;
using std::tuple;
using std::uniform_int_distribution;
using std::variant;
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
    // x[i] = j -> y[j] = i, and when the arrays are the same length, y[j] = i ->
    // x[i] = j too. The shorter-first injection form says nothing about an entry
    // of y that no entry of x names, not even that its value is one of x's
    // indices.
    //
    // Random sweeps may pick domains that include out-of-range values; the
    // propagator's prepare() trims them but the brute-force predicate runs over
    // raw enumerated values, so we need explicit bounds checks before the .at()
    // calls. x's values are y's indices, numbered from y_start, and the other
    // way around.
    auto inverse_holds(const vector<int> & x, const vector<int> & y, int x_start, int y_start) -> bool
    {
        for (const auto & [i, _] : enumerate(x)) {
            if (x.at(i) - y_start < 0 || std::cmp_greater_equal(x.at(i) - y_start, y.size()))
                return false;
            if (cmp_not_equal(y.at(x.at(i) - y_start) - x_start, i))
                return false;
        }
        if (x.size() == y.size())
            for (const auto & [i, _] : enumerate(y)) {
                if (y.at(i) - x_start < 0 || std::cmp_greater_equal(y.at(i) - x_start, x.size()))
                    return false;
                if (cmp_not_equal(x.at(y.at(i) - x_start) - y_start, i))
                    return false;
            }
        return true;
    }
}

auto run_inverse_test(bool proofs, const ViewWrapConfig & view_cfg, const vector<variant<int, pair<int, int>>> & x_range,
    const vector<variant<int, pair<int, int>>> & y_range, int x_start, int y_start) -> void
{
    auto wraps = wraps_for_positions(view_cfg, static_cast<int>(x_range.size() + y_range.size()));
    print(cerr, "inverse [{}] {} {} starts {} {}{}", view_wrap_config_label(view_cfg), x_range, y_range, x_start, y_start,
        proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<vector<int>, vector<int>>> expected, actual;
    build_expected(expected, [&](const vector<int> & x, const vector<int> & y) { return inverse_holds(x, y, x_start, y_start); }, x_range, y_range);

    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> x, y;
    std::size_t pos = 0;
    for (const auto & entry : x_range) {
        auto w = wraps.at(pos++);
        x.push_back(visit([&](auto e) { return create_integer_variable_or_constant_with_view(p, e, w); }, entry));
    }
    for (const auto & entry : y_range) {
        auto w = wraps.at(pos++);
        y.push_back(visit([&](auto e) { return create_integer_variable_or_constant_with_view(p, e, w); }, entry));
    }
    p.post(Inverse{x, y, Integer(x_start), Integer(y_start)});

    auto proof_name = proofs ? make_optional("inverse_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{x, y});

    check_results(proof_name, expected, actual);
}

// The same variable in more than one entry. Each entry of x and of y names one
// of the unique variables, and the brute force runs over those, so it sees the
// aliasing. A repeat within x, or within y when the arrays are the same length,
// is unsatisfiable and gets a root contradiction; within y in the injection
// form it is satisfiable, as long as at most one of the two entries is named.
//
// An entry of x can also be a view, the unique variable plus an offset, so that
// two entries can be views of one variable.
auto run_inverse_aliased_test(bool proofs, const vector<pair<int, int>> & unique_domains, const vector<int> & x_positions,
    const vector<int> & y_positions, const vector<int> & x_offsets = {}) -> void
{
    print(cerr, "inverse aliased {} x {} offsets {} y {}{}", unique_domains, x_positions, x_offsets, y_positions, proofs ? " with proofs:" : ":");
    cerr << flush;

    auto offset_of = [&](size_t i) { return i < x_offsets.size() ? x_offsets[i] : 0; };
    auto pick = [](const vector<int> & u, const vector<int> & positions, const auto & offset) {
        vector<int> result;
        for (const auto & [i, p] : enumerate(positions))
            result.push_back(u.at(p) + offset(i));
        return result;
    };
    auto no_offset = [](size_t) { return 0; };

    vector<variant<int, pair<int, int>>> ranges;
    for (const auto & d : unique_domains)
        ranges.emplace_back(d);
    set<tuple<vector<int>>> expected, actual;
    build_expected(
        expected, [&](const vector<int> & u) { return inverse_holds(pick(u, x_positions, offset_of), pick(u, y_positions, no_offset), 0, 0); },
        ranges);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> unique_vars;
    for (const auto & [lo, hi] : unique_domains)
        unique_vars.push_back(p.create_integer_variable(Integer(lo), Integer(hi)));
    vector<IntegerVariableID> x, y;
    for (const auto & [i, pos] : enumerate(x_positions))
        x.push_back(unique_vars.at(pos) + Integer(offset_of(i)));
    for (auto pos : y_positions)
        y.push_back(unique_vars.at(pos));
    p.post(Inverse{x, y});

    auto proof_name = proofs ? make_optional("inverse_test_aliased") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{unique_vars});
    check_results(proof_name, expected, actual);
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    // Combined x|y operand positions wrapped by the single-position sweep.
    // The fixed and random data have several arrays whose combined length
    // reaches into this range; a single-position index beyond it would wrap
    // nothing on any test, so detect and skip rather than emit a duplicate
    // bare run. The mixed/uniform policies wrap every position regardless.
    constexpr int n_positions = 6;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "inverse view sweep: position {} out of range for n_positions = {}; skipping", *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    using Entry = variant<int, pair<int, int>>;
    vector<tuple<vector<Entry>, vector<Entry>>> var_data = {// Boundary: empty arrays — vacuously satisfied.
        {{}, {}},                                           //
        // Boundary: singleton — forces both to 0.
        {{pair{0, 0}}, {pair{0, 0}}}, //
        {{pair{0, 5}}, {pair{0, 5}}}, //
        // Existing hand-rolled cases.
        {{pair{0, 2}, pair{0, 2}, pair{0, 2}}, {pair{0, 2}, pair{0, 2}, pair{0, 2}}},                                                 //
        {{pair{0, 2}, pair{1, 3}, pair{0, 2}, pair{0, 3}}, {pair{0, 3}, pair{1, 2}, pair{1, 3}, pair{0, 3}}},                         //
        {{pair{0, 2}, pair{0, 2}, pair{0, 2}, pair{0, 4}, pair{0, 4}}, {pair{0, 4}, pair{0, 4}, pair{0, 4}, pair{3, 4}, pair{3, 4}}}, //
        // Constant entries pin one inverse pair.
        {{1, pair{0, 2}, pair{0, 2}}, {pair{0, 2}, 0, pair{0, 2}}},                         //
        {{pair{0, 3}, pair{0, 3}, 0, pair{0, 3}}, {2, pair{0, 3}, pair{0, 3}, pair{0, 3}}}, //
        // Issue #171 regression: two array positions pinned to the same constant
        // makes the constraint infeasible (Inverse forces a permutation). The
        // recovered "AM1" line for the duplicate-pinned value is now a direct
        // `0 ≥ 1` contradiction, which downstream pol expressions sum into a
        // valid contradiction proof.
        {{3, 2, 3, pair{0, 3}}, {pair{0, 3}, pair{0, 3}, pair{0, 3}, pair{0, 3}}},          //
        {{pair{0, 3}, pair{0, 3}, pair{0, 3}, pair{0, 3}}, {1, pair{0, 3}, 1, pair{0, 3}}}, //
        // issue #254: fully all-constant arguments, both directions.
        {{0, 1}, {0, 1}}, // identity permutation, consistent (tautology)
        {{1, 0}, {1, 0}}, // swap: x[0]=1<->y[1]=0, x[1]=0<->y[0]=1, consistent (tautology)
        {{1, 0}, {0, 1}}, // x swapped but y identity: inconsistent (contradiction)
        // Injection form: x shorter than y, and only x[i] = j -> y[j] = i. The
        // issue #1047 instance, which ACE gives 12 solutions: y's third entry is
        // free whenever nothing names it.
        {{pair{0, 2}, pair{0, 2}}, {pair{0, 1}, pair{0, 1}, pair{0, 1}}}, //
        // An entry of y that nothing names can take a value outside x's indices
        // (36 solutions, as ACE says), and one that must be named cannot.
        {{pair{0, 2}, pair{0, 2}}, {pair{0, 5}, pair{0, 5}, pair{0, 5}}}, //
        {{pair{0, 1}, pair{0, 1}, pair{0, 3}}, {pair{-1, 3}, pair{-1, 3}, pair{-1, 3}, pair{-1, 3}}},
        {{pair{0, 3}}, {pair{0, 1}, pair{0, 1}, pair{0, 1}, pair{0, 1}}}, //
        {{}, {pair{0, 1}, pair{0, 1}}},                                   //
        {{1, pair{0, 3}}, {pair{0, 2}, pair{0, 2}, pair{0, 2}, pair{-1, 2}}},
        // Three entries of x share three values, so y's first three entries
        // cannot name the fourth index, which no entry of x has. Seeing that
        // takes a pigeonhole, not unit propagation, so these are the cases that
        // the Hall sum is load-bearing for: first alone, then beside an entry
        // that takes none of those values, then beside a constant, whose value
        // is a Hall set of its own.
        {{pair{0, 2}, pair{0, 2}, pair{0, 2}}, {pair{0, 3}, pair{0, 3}, pair{0, 3}, pair{0, 3}}},
        {{pair{0, 2}, pair{0, 2}, pair{0, 2}, pair{3, 4}}, {pair{0, 4}, pair{0, 4}, pair{0, 4}, pair{0, 4}, pair{0, 4}}},
        {{3, pair{0, 2}, pair{0, 2}, pair{0, 2}}, {pair{0, 4}, pair{0, 4}, pair{0, 4}, pair{0, 4}, pair{0, 4}}},
        // Two components, {0, 1} and {2, 3, 4}, which each prune y by themselves.
        {{pair{0, 1}, pair{0, 1}, pair{2, 4}, pair{2, 4}, pair{2, 4}}, {pair{0, 2}, pair{0, 2}, pair{0, 5}, pair{0, 5}, pair{0, 5}, pair{0, 1}}}};

    mt19937 rand(*get_seed());

    // Random sweep: equal-length arrays of length 2..4 with domains over
    // {0..n-1} (occasionally const). Inverse forces a permutation matching,
    // so the constraint is selective — but the brute-force enumerator runs
    // n^n × n^n combinations before filtering, which is 4^4 × 4^4 = 65 536
    // for n=4. Stays sub-second.
    uniform_int_distribution n_dist{2, 4};
    for (int x_count = 0; x_count < 8; ++x_count) {
        int n = n_dist(rand);
        vector<Entry> x_doms, y_doms;
        for (int i = 0; i < n; ++i) {
            x_doms.emplace_back(generate_random_data_item(rand, random_bounds_or_constant(0, 0, n - 1, n - 1)));
            y_doms.emplace_back(generate_random_data_item(rand, random_bounds_or_constant(0, 0, n - 1, n - 1)));
        }
        var_data.emplace_back(x_doms, y_doms);
    }

    // And the injection form: x of length 1..3 into y's indices, with y one or
    // two longer. y's domains stray a little outside x's indices, which an entry
    // that nothing names may take.
    uniform_int_distribution m_dist{1, 3}, extra_dist{1, 2};
    for (int x_count = 0; x_count < 8; ++x_count) {
        int m = m_dist(rand), n = m + extra_dist(rand);
        vector<Entry> x_doms, y_doms;
        for (int i = 0; i < m; ++i)
            x_doms.emplace_back(generate_random_data_item(rand, random_bounds_or_constant(0, 0, n - 1, n - 1)));
        for (int j = 0; j < n; ++j)
            y_doms.emplace_back(generate_random_data_item(rand, random_bounds_or_constant(-1, 0, m, m + 1)));
        var_data.emplace_back(x_doms, y_doms);
    }

    // Every case also runs again with the arrays numbered from somewhere other
    // than zero. x's values are y's indices and the other way around, so x's
    // domains move by y_start and y's by x_start. Two of the three pairs have
    // x_start != y_start, which the propagator's value set once got wrong: it
    // numbered x's values from x_start, and so failed at the root on every
    // such instance. MiniZinc's 1-based arrays give the first pair.
    auto shifted = [](const vector<Entry> & entries, int by) {
        vector<Entry> result;
        for (const auto & e : entries) {
            if (auto c = get_if<int>(&e))
                result.emplace_back(*c + by);
            else {
                auto [lo, hi] = get<pair<int, int>>(e);
                result.emplace_back(pair{lo + by, hi + by});
            }
        }
        return result;
    };
    const vector<pair<int, int>> other_starts = {{1, 1}, {3, -2}, {-2, 4}};

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (const auto & [idx, data] : enumerate(var_data)) {
            const auto & [x, y] = data;
            run_inverse_test(proofs, view_cfg, x, y, 0, 0);
            auto [x_start, y_start] = other_starts.at(idx % other_starts.size());
            run_inverse_test(proofs, view_cfg, shifted(x, y_start), shifted(y, x_start), x_start, y_start);
        }
    }

    // The aliased cases build their own variables and wrap none of them, so run
    // them once, in the bare configuration: the view-wrapped runs are separate
    // ctest cases in the same directory, and would race on the proof files.
    for (bool proofs : {false, true}) {
        if (! view_wrap_config_is_effectively_bare(view_cfg, n_positions))
            break;
        if (proofs && ! can_run_veripb())
            continue;
        // A repeat within x, bijection and injection.
        run_inverse_aliased_test(proofs, {{0, 2}, {0, 2}, {0, 2}, {0, 2}, {0, 2}}, {0, 1, 0}, {2, 3, 4});
        run_inverse_aliased_test(proofs, {{0, 2}, {0, 2}, {0, 2}, {0, 2}}, {0, 0}, {1, 2, 3});
        // A repeat within y: unsatisfiable as a bijection, not as an injection.
        run_inverse_aliased_test(proofs, {{0, 2}, {0, 2}, {0, 2}, {0, 2}, {0, 2}}, {0, 1, 2}, {3, 4, 4});
        run_inverse_aliased_test(proofs, {{0, 2}, {0, 2}, {0, 1}, {0, 1}}, {0, 1}, {2, 2, 3});
        // Across the two arrays, which is legitimate: inverse(x, x) is an
        // involution.
        run_inverse_aliased_test(proofs, {{0, 2}, {0, 2}, {0, 2}}, {0, 1, 2}, {0, 1, 2});
        // Two and three views of one variable in x, in the injection form.
        run_inverse_aliased_test(proofs, {{0, 1}, {0, 2}, {0, 3}, {0, 3}, {0, 3}, {0, 3}}, {0, 0, 1}, {2, 3, 4, 5}, {0, 1, 0});
        run_inverse_aliased_test(proofs, {{0, 1}, {0, 4}, {-1, 4}, {-1, 4}, {-1, 4}, {-1, 4}}, {0, 0, 0}, {2, 3, 4, 5}, {0, 1, 2});
    }

    {
        // x is all different and valued in y's indices, so it cannot be longer.
        Problem p;
        auto x = p.create_integer_variable_vector(3, 0_i, 2_i);
        auto y = p.create_integer_variable_vector(2, 0_i, 2_i);
        bool threw = false;
        try {
            p.post(Inverse{x, y});
        }
        catch (const InvalidProblemDefinitionException &) {
            threw = true;
        }
        if (! threw) {
            cerr << "expected Inverse with a longer first array to throw\n";
            return EXIT_FAILURE;
        }
    }

    return EXIT_SUCCESS;
}
