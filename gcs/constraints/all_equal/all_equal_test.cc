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
using std::set;
using std::string;
using std::tuple;
using std::variant;
using std::vector;
using std::visit;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
using fmt::println;
#endif

using namespace gcs;
using namespace gcs::test_innards;

auto run_test(bool proofs, const ViewWrapConfig & view_cfg, const vector<pair<int, int>> & domains) -> void
{
    auto wraps = wraps_for_positions(view_cfg, static_cast<int>(domains.size()));
    print(cerr, "all_equal [{}] domains={}{}", view_wrap_config_label(view_cfg), domains, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<vector<int>>> expected, actual;
    build_expected(
        expected,
        [](const vector<int> & vs) {
            for (size_t i = 1; i < vs.size(); ++i)
                if (vs[i] != vs[0])
                    return false;
            return true;
        },
        domains);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> vars;
    for (std::size_t i = 0; i < domains.size(); ++i)
        vars.push_back(create_integer_variable_or_constant_with_view(p, domains[i], wraps.at(i)));
    p.post(AllEqual{vars});

    auto proof_name = proofs ? make_optional("all_equal_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{vars});
    check_results(proof_name, expected, actual);
}

// issue #254: AllEqual over a degenerate collection — empty / single-element
// (both vacuously satisfiable, no propagator) and tiny all-genuine-constant
// arrays (ConstantIntegerVariableID) in both the equal (SAT) and unequal
// (UNSAT) directions, plus a mixed const+variable case.
auto run_all_equal_collection_test(bool proofs, const string & label, const vector<variant<int, pair<int, int>>> & specs) -> void
{
    print(cerr, "all_equal_collection [{}] {}{}", label, specs, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<vector<int>>> expected, actual;
    build_expected(
        expected,
        [](const vector<int> & vs) {
            for (std::size_t i = 1; i < vs.size(); ++i)
                if (vs[i] != vs[0])
                    return false;
            return true;
        },
        specs);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> vars;
    for (const auto & s : specs)
        vars.push_back(visit([&](auto b) { return create_integer_variable_or_constant(p, b); }, s));
    p.post(AllEqual{vars});

    auto proof_name = proofs ? make_optional("all_equal_test_collection") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{vars});
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
                    if (u == v)
                        return true;
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

// Dup-variable test: AllEqual with the same handle in several positions.
// Duplicates are idempotent (x = x is vacuous); the constraint reduces to
// AllEqual over the unique vars. Consistency isn't checked on dup runs;
// see tmp/duplicate_var_audit.md.
auto run_dup_all_equal_test(bool proofs, const vector<pair<int, int>> & unique_domains, const vector<int> & positions) -> void
{
    print(cerr, "all_equal dup domains={} positions={}{}", unique_domains, positions, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<vector<int>>> expected, actual;
    build_expected(
        expected,
        [&](const vector<int> & vals) -> bool {
            // After dup-collapse, AllEqual still requires all referenced
            // values to be equal: every position's variable's value must
            // match position 0's.
            int v0 = vals.at(positions.at(0));
            for (auto pos : positions)
                if (vals.at(pos) != v0)
                    return false;
            return true;
        },
        unique_domains);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> unique_vars;
    for (const auto & d : unique_domains)
        unique_vars.push_back(p.create_integer_variable(Integer(d.first), Integer(d.second)));
    vector<IntegerVariableID> posted;
    for (auto pos : positions)
        posted.push_back(unique_vars.at(pos));
    p.post(AllEqual{posted});

    auto proof_name = proofs ? make_optional("all_equal_test_dup") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{unique_vars});
    check_results(proof_name, expected, actual);
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    // Max vector length across the data is 4; CMake registers up through
    // position 3. Out-of-range single positions degrade to all-bare via the
    // helper, which we detect and skip.
    constexpr int n_positions = 4;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "all_equal view sweep: position {} out of range for n_positions = {}; skipping", *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    bool run_holes = view_wrap_config_is_effectively_bare(view_cfg, n_positions);

    vector<vector<pair<int, int>>> data = {
        {{1, 5}, {3, 8}},
        {{1, 3}, {5, 8}},
        {{1, 4}, {1, 4}},
        {{1, 5}, {2, 6}, {3, 7}},
        {{2, 4}, {2, 4}, {2, 4}},
        {{1, 6}, {2, 5}, {3, 4}, {4, 7}},
        // issue #254: all-fixed (singleton-domain) collections, both directions.
        {{3, 3}, {3, 3}},         // equal constants (tautology)
        {{2, 2}, {5, 5}},         // unequal constants (contradiction)
        {{4, 4}, {4, 4}, {4, 4}}, // three equal constants (tautology)
    };

    mt19937 rand(*get_seed());
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
    for (int i = 0; i < 5; ++i)
        random_run(2);
    for (int i = 0; i < 5; ++i)
        random_run(3);
    for (int i = 0; i < 3; ++i)
        random_run(4);

    bool run_dup = view_wrap_config_is_effectively_bare(view_cfg, n_positions);

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (const auto & doms : data)
            run_test(proofs, view_cfg, doms);
        if (run_holes)
            run_holes_test(proofs);
        if (view_wrap_config_is_effectively_bare(view_cfg, n_positions)) {
            // Degenerate collections with genuine constants (issue #254).
            run_all_equal_collection_test(proofs, "empty", {});
            run_all_equal_collection_test(proofs, "single_var", {pair{0, 2}});
            run_all_equal_collection_test(proofs, "single_const", {5});
            run_all_equal_collection_test(proofs, "const_equal", {3, 3, 3});
            run_all_equal_collection_test(proofs, "const_unequal", {3, 4});
            run_all_equal_collection_test(proofs, "mixed", {3, pair{1, 5}, 3});
        }
        if (run_dup) {
            // {x, x} — tautology, every value of x.
            run_dup_all_equal_test(proofs, {{1, 5}}, {0, 0});
            // {x, x, y} — reduces to AllEqual({x, y}); intersection of domains.
            run_dup_all_equal_test(proofs, {{1, 5}, {3, 7}}, {0, 0, 1});
            // {x, y, x} — same as above with reordering.
            run_dup_all_equal_test(proofs, {{1, 5}, {3, 7}}, {0, 1, 0});
            // {x, y, x, y} — reduces to AllEqual({x, y}).
            run_dup_all_equal_test(proofs, {{2, 6}, {1, 4}}, {0, 1, 0, 1});
            // Disjoint domains via dup — UNSAT.
            run_dup_all_equal_test(proofs, {{1, 3}, {5, 7}}, {0, 1, 0});
        }
    }

    return EXIT_SUCCESS;
}
