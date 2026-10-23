#include <gcs/constraints/among.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <util/overloaded.hh>

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
#include <fmt/std.h>
#endif

using std::cerr;
using std::count;
using std::count_if;
using std::flush;
using std::make_optional;
using std::mt19937;
using std::nullopt;
using std::pair;
using std::set;
using std::string;
using std::to_string;
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

auto run_among_test(bool proofs, const ViewWrapConfig & view_cfg, variant<int, pair<int, int>> result_range, const vector<int> & voi,
    const vector<variant<int, pair<int, int>>> & array_range) -> void
{
    // Position 0 = result, 1..N = array entries. voi is a value set, not
    // variables, so it stays as-is.
    int n_positions = 1 + static_cast<int>(array_range.size());
    auto wraps = wraps_for_positions(view_cfg, n_positions);
    visit(
        [&](auto result) {
            print(cerr, "among [{}] {} {} {} {}", view_wrap_config_label(view_cfg), result, voi, array_range, proofs ? " with proofs:" : ":");
        },
        result_range);
    cerr << flush;

    auto is_satisfying = [&](int n, const vector<int> & a) {
        return n == count_if(a.begin(), a.end(), [&](int v) { return 0 != count(voi.begin(), voi.end(), v); });
    };

    set<tuple<int, vector<int>>> expected, actual;
    build_expected(expected, is_satisfying, result_range, array_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto result = visit([&](auto r) { return create_integer_variable_or_constant_with_view(p, r, wraps.at(0)); }, result_range);
    vector<IntegerVariableID> array;
    for (std::size_t i = 0; i < array_range.size(); ++i)
        array.push_back(visit([&](auto a) { return create_integer_variable_or_constant_with_view(p, a, wraps.at(i + 1)); }, array_range[i]));
    vector<Integer> voi_i;
    for (const auto & v : voi)
        voi_i.push_back(Integer(v));
    p.post(Among{array, voi_i, result});

    auto proof_name = proofs ? make_optional("among_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_consistency(
        p, proof_name, expected, actual, tuple{pair{result, CheckConsistency::GAC}, pair{array, CheckConsistency::GAC}});

    check_results(proof_name, expected, actual);
}

// Dup-variable test: Among with the same handle appearing in several
// array positions. Each occurrence is counted independently (so a fixed
// duplicated variable contributes its membership multiple times). See
// tmp/duplicate_var_audit.md.
auto run_dup_among_test(bool proofs, const vector<pair<int, int>> & unique_domains, const vector<int> & positions, const vector<int> & voi,
    pair<int, int> result_range) -> void
{
    print(cerr, "among dup domains={} positions={} voi={} result={}{}", unique_domains, positions, voi, result_range, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, vector<int>>> expected, actual;
    build_expected(
        expected,
        [&](int r, const vector<int> & vals) -> bool {
            int counted = 0;
            for (auto pos : positions)
                if (0 != count(voi.begin(), voi.end(), vals.at(pos)))
                    ++counted;
            return r == counted;
        },
        result_range, unique_domains);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto result = p.create_integer_variable(Integer(result_range.first), Integer(result_range.second));
    vector<IntegerVariableID> unique_vars;
    for (const auto & d : unique_domains)
        unique_vars.push_back(p.create_integer_variable(Integer(d.first), Integer(d.second)));
    vector<IntegerVariableID> array;
    for (auto pos : positions)
        array.push_back(unique_vars.at(pos));
    vector<Integer> voi_i;
    for (auto v : voi)
        voi_i.push_back(Integer(v));
    p.post(Among{array, voi_i, result});

    auto proof_name = proofs ? make_optional("among_test_dup") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{result, unique_vars});
    check_results(proof_name, expected, actual);
}

// Self-reference: the result variable also appears in the array.
auto run_self_ref_among_test(bool proofs, pair<int, int> shared_range, const vector<int> & voi) -> void
{
    print(cerr, "among self-ref shared={} voi={}{}", shared_range, voi, proofs ? " with proofs:" : ":");
    cerr << flush;

    // Array is [shared, shared] and count is shared too — count = how many
    // occurrences of shared's value are in voi, times 2; plus shared itself
    // must equal that count.
    set<tuple<int>> expected, actual;
    build_expected(
        expected,
        [&](int s) -> bool {
            int hits = (0 != count(voi.begin(), voi.end(), s)) ? 2 : 0;
            return s == hits;
        },
        shared_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto shared = p.create_integer_variable(Integer(shared_range.first), Integer(shared_range.second));
    vector<Integer> voi_i;
    for (auto v : voi)
        voi_i.push_back(Integer(v));
    p.post(Among{vector<IntegerVariableID>{shared, shared}, voi_i, shared});

    auto proof_name = proofs ? make_optional("among_test_selfref") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{shared});
    check_results(proof_name, expected, actual);
}

// A position or how_many in run_aliased_among_test: an index into the shared
// variables, a constant, or a view of a shared variable (negated first if
// asked, then offset).
struct AliasedConstant
{
    int value;
};
struct AliasedView
{
    int index;
    bool negate;
    int offset;
};
using AliasedEntry = variant<int, AliasedConstant, AliasedView>;

// how_many sharing a variable with a position, directly or through a view, over
// shared variables built from value lists (issue #1308). The lower bound on
// how_many is justified by an at-least-one over the values of interest each
// must-match position can still take. Once a definition range is wider than the
// tracker's cover threshold that line is keyed on those values, and the
// single-literal inference used to read them after its own push had moved
// how_many, and so the position; VeriPB then rejected the proof. Solved under the
// harness's branching and then under the default branching, since the bad
// inferences depend on the search path.
auto run_aliased_among_test(bool proofs, const vector<vector<int>> & shared_domains, const vector<AliasedEntry> & positions, const vector<int> & voi,
    AliasedEntry how_many) -> void
{
    auto label = [](const AliasedEntry & e) -> string {
        return overloaded{
            [](int i) { return "u" + to_string(i); },                                                              //
            [](AliasedConstant c) { return to_string(c.value); },                                                  //
            [](AliasedView v) { return (v.negate ? "-u" : "u") + to_string(v.index) + "+" + to_string(v.offset); } //
        }
            .visit(e);
    };
    string positions_label;
    for (const auto & e : positions)
        positions_label += (positions_label.empty() ? "" : ",") + label(e);
    print(cerr, "among aliased domains={} positions={} voi={} how_many={}{}", shared_domains, positions_label, voi, label(how_many),
        proofs ? " with proofs:" : ":");
    cerr << flush;

    auto value_of = [](const AliasedEntry & e, const vector<int> & vals) -> int {
        return overloaded{
            [&](int i) { return vals.at(i); },                                                          //
            [](AliasedConstant c) { return c.value; },                                                  //
            [&](AliasedView v) { return (v.negate ? -vals.at(v.index) : vals.at(v.index)) + v.offset; } //
        }
            .visit(e);
    };
    vector<variant<int, pair<int, int>, vector<int>>> domain_specs(shared_domains.begin(), shared_domains.end());
    set<tuple<vector<int>>> expected, actual;
    build_expected(
        expected,
        [&](const vector<int> & vals) -> bool {
            int counted = 0;
            for (const auto & e : positions)
                if (0 != count(voi.begin(), voi.end(), value_of(e, vals)))
                    ++counted;
            return counted == value_of(how_many, vals);
        },
        domain_specs);
    println(cerr, " expecting {} solutions", expected.size());

    auto post = [&](Problem & p) -> vector<IntegerVariableID> {
        vector<IntegerVariableID> shared;
        for (const auto & d : shared_domains) {
            vector<Integer> values;
            for (auto v : d)
                values.push_back(Integer(v));
            shared.push_back(p.create_integer_variable(values));
        }
        auto var_of = [&](const AliasedEntry & e) -> IntegerVariableID {
            return overloaded{
                [&](int i) -> IntegerVariableID { return shared.at(i); },                                           //
                [](AliasedConstant c) -> IntegerVariableID { return ConstantIntegerVariableID{Integer(c.value)}; }, //
                [&](AliasedView v) -> IntegerVariableID {
                    return v.negate ? -shared.at(v.index) + Integer(v.offset) : shared.at(v.index) + Integer(v.offset);
                } //
            }
                .visit(e);
        };
        vector<IntegerVariableID> array;
        for (const auto & e : positions)
            array.push_back(var_of(e));
        vector<Integer> voi_i;
        for (auto v : voi)
            voi_i.push_back(Integer(v));
        p.post(Among{array, voi_i, var_of(how_many)});
        return shared;
    };

    auto proof_name = proofs ? make_optional("among_test_aliased") : nullopt;
    {
        Problem p;
        auto shared = post(p);
        solve_for_tests(p, proof_name, actual, tuple{shared});
        check_results(proof_name, expected, actual);
    }
    {
        Problem p;
        auto shared = post(p);
        actual.clear();
        last_run_truncated() = false;
        solve_with(p,
            SolveCallbacks{
                .solution = [&](const CurrentState & s) -> bool { return actual.emplace(extract_from_state(s, shared)), true; }, //
                .stats_report = silent_stats_report()                                                                            //
            },
            proof_name ? make_optional<ProofOptions>(ProofFileNames{*proof_name}) : nullopt);
        check_results(proof_name, expected, actual);
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    constexpr int n_positions = 5;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "among view sweep: position {} out of range for n_positions = {}; skipping", *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    vector<tuple<variant<int, pair<int, int>>, vector<int>, vector<variant<int, pair<int, int>>>>> data = {
        {pair{1, 3}, vector{2, 4, 6, 8}, {pair{1, 10}, pair{1, 10}, pair{1, 10}}}, //
        {pair{1, 5}, vector{1, 2, 3}, {pair{1, 5}, pair{1, 5}, pair{1, 5}}},       //
        {pair{1, 1}, vector{1, 2, 3}, {pair{1, 5}, pair{1, 5}, pair{1, 5}}},       //
        {pair{3, 5}, vector{1, 3}, {pair{1, 2}, pair{1, 2}, pair{1, 5}}},          //
        {pair{0, 5}, vector{1, 3}, {pair{1, 2}, pair{1, 2}, pair{1, 5}}},          //
        {pair{1, 5}, vector{2, 3, 2, 3, 3}, {pair{1, 5}, pair{1, 5}, pair{1, 5}}}, //
        // Degenerate cases (issue #254): empty array, empty value set,
        // single element, all-constant. Result is a genuine constant.
        {0, vector{2, 3}, {}},                     // empty array: 0 in set (tautology)
        {1, vector{2, 3}, {}},                     // empty array: can't be 1 (contradiction)
        {0, vector<int>{}, {5, 5, 5}},             // empty value set: nothing matches (tautology)
        {1, vector<int>{}, {5, 5, 5}},             // empty value set: can't be 1 (contradiction)
        {1, vector{5}, {5}},                       // single element matches (tautology)
        {1, vector{5}, {6}},                       // single element, no match (contradiction)
        {2, vector{5, 6}, {5, 6, 7}},              // all-constant array: 2 match (tautology)
        {3, vector{5, 6}, {5, 6, 7}},              // all-constant array: only 2 match (contradiction)
        {pair{0, 2}, vector{5}, {5, pair{1, 10}}}, // mixed: one constant match + one variable
        // Bit-aliased {0,1}-domain array variables with a value-of-interest set
        // that contains both 0 and 1 plus another value, ordered so the
        // complementary pair (var != 0 = b0, var != 1 = ~b0) is NOT first in the
        // per-variable at-most-one. Among tolerates the loose pre-#557 line, so
        // this does not fail without the fix, but it exercises the fixed
        // recover_am1 block scheme on the Top-level (cached-initialiser) path that
        // the GlobalCardinality demand aggregate shares at Temporary level.
        {pair{0, 3}, vector{5, 0, 1}, {pair{0, 1}, pair{0, 5}, pair{0, 1}}}};

    mt19937 rand(*get_seed());
    for (int x = 0; x < 10; ++x) {
        uniform_int_distribution n_values_dist(1, 4);
        auto n_values_1 = n_values_dist(rand);
        auto n_values_2 = n_values_dist(rand);
        uniform_int_distribution values_dist(-10, 10);
        generate_random_data(rand, data, random_bounds(-7, 7, 5, 10), vector{size_t(n_values_1), values_dist},
            vector{size_t(n_values_2), random_bounds_or_constant(-5, 8, 3, 8)});
    }

    bool run_dup = view_wrap_config_is_effectively_bare(view_cfg, n_positions);

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & [r1, r2, r3] : data)
            run_among_test(proofs, view_cfg, r1, r2, r3);
        if (run_dup) {
            // {x, x, y} — x's match counts twice.
            run_dup_among_test(proofs, {{1, 4}, {1, 4}}, {0, 0, 1}, {2, 3}, {0, 3});
            // {x, y, x} — order shouldn't matter.
            run_dup_among_test(proofs, {{1, 4}, {1, 4}}, {0, 1, 0}, {2, 3}, {0, 3});
            // {x, x} — count must be 0 or 2.
            run_dup_among_test(proofs, {{0, 5}}, {0, 0}, {1, 3, 5}, {0, 2});
            // Self-reference: result var also in array.
            run_self_ref_among_test(proofs, {0, 4}, {2});
            run_self_ref_among_test(proofs, {0, 3}, {0, 2});

            // how_many among the positions over a definition range wider than
            // 100 values (issue #1308), directly and through views.
            using C = AliasedConstant;
            using V = AliasedView;
            run_aliased_among_test(proofs, {{-98, 1, 2}}, {0, 0, 0}, {1, 2}, 0);
            run_aliased_among_test(proofs, {{-98, 1, 2, 3}}, {0, 0, 0}, {1, 2, 3}, 0);
            run_aliased_among_test(proofs, {{1, 2, 3, 103}}, {0, 0, 0}, {1, 2, 3}, 0);
            run_aliased_among_test(proofs, {{1, 2, 3, 103}}, {0, 0, 0}, {1, 2}, 0);
            // A range of exactly 100 values: the per-value at-least-one.
            run_aliased_among_test(proofs, {{-97, 1, 2}}, {0, 0, 0}, {1, 2}, 0);
            // A position is a view of how_many, or how_many a view of a position.
            run_aliased_among_test(proofs, {{1, 2, 3, 110}}, {C{1}, V{0, false, -3}, 0, 0}, {1, 2, 3}, 0);
            run_aliased_among_test(proofs, {{0, 1, 108}}, {V{0, true, 1}, 0, V{0, false, 1}}, {0, 1}, 0);
            run_aliased_among_test(proofs, {{0, 1, 2, 3, 111}}, {0, C{2}, C{5}, 0}, {0, 1, 2}, V{0, true, 3});
            run_aliased_among_test(proofs, {{-102, 2, 4}}, {0, 0, C{-1}, 0, C{-1}}, {2, 4}, V{0, false, -2});
        }
    }

    return EXIT_SUCCESS;
}
