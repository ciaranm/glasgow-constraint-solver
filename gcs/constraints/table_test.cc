#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/table.hh>
#include <gcs/extensional.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <util/overloaded.hh>

#include <cstdlib>
#include <iostream>
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

auto run_table_test_2(bool proofs, const ViewWrapConfig & view_cfg, pair<int, int> r1, pair<int, int> r2, SimpleTuples allowed) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 2);
    print(cerr, "table 2var [{}] [{},{}] [{},{}] {} tuples{}",
        view_wrap_config_label(view_cfg), r1.first, r1.second, r2.first, r2.second, allowed.size(), proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, int>> expected, actual;
    build_expected(expected, [&](int a, int b) -> bool {
        for (const auto & t : allowed)
            if (t[0].raw_value == a && t[1].raw_value == b)
                return true;
        return false;
    }, r1, r2);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = create_integer_variable_or_constant_with_view(p, r1, wraps.at(0));
    auto v2 = create_integer_variable_or_constant_with_view(p, r2, wraps.at(1));
    p.post(Table{{v1, v2}, allowed});

    auto proof_name = proofs ? make_optional("table_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2});
    check_results(proof_name, expected, actual);
}

auto run_table_test_3(bool proofs, const ViewWrapConfig & view_cfg, pair<int, int> r1, pair<int, int> r2, pair<int, int> r3, SimpleTuples allowed) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 3);
    print(cerr, "table 3var [{}] [{},{}] [{},{}] [{},{}] {} tuples{}",
        view_wrap_config_label(view_cfg), r1.first, r1.second, r2.first, r2.second, r3.first, r3.second, allowed.size(), proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, int, int>> expected, actual;
    build_expected(expected, [&](int a, int b, int c) -> bool {
        for (const auto & t : allowed)
            if (t[0].raw_value == a && t[1].raw_value == b && t[2].raw_value == c)
                return true;
        return false;
    }, r1, r2, r3);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = create_integer_variable_or_constant_with_view(p, r1, wraps.at(0));
    auto v2 = create_integer_variable_or_constant_with_view(p, r2, wraps.at(1));
    auto v3 = create_integer_variable_or_constant_with_view(p, r3, wraps.at(2));
    p.post(Table{{v1, v2, v3}, allowed});

    auto proof_name = proofs ? make_optional("table_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2, v3});
    check_results(proof_name, expected, actual);
}

auto run_wildcard_table_test(bool proofs, const ViewWrapConfig & view_cfg, pair<int, int> r1, pair<int, int> r2, pair<int, int> r3, WildcardTuples allowed) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 3);
    print(cerr, "wildcard table [{}] [{},{}] [{},{}] [{},{}] {} tuples{}",
        view_wrap_config_label(view_cfg), r1.first, r1.second, r2.first, r2.second, r3.first, r3.second, allowed.size(), proofs ? " with proofs:" : ":");
    cerr << flush;

    auto entry_matches = [](const IntegerOrWildcard & entry, int val) -> bool {
        return overloaded{
            [val](Integer i) { return i.raw_value == val; },
            [](Wildcard) { return true; }}
            .visit(entry);
    };

    set<tuple<int, int, int>> expected, actual;
    build_expected(expected, [&](int a, int b, int c) -> bool {
        for (const auto & t : allowed)
            if (entry_matches(t[0], a) && entry_matches(t[1], b) && entry_matches(t[2], c))
                return true;
        return false;
    }, r1, r2, r3);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = create_integer_variable_or_constant_with_view(p, r1, wraps.at(0));
    auto v2 = create_integer_variable_or_constant_with_view(p, r2, wraps.at(1));
    auto v3 = create_integer_variable_or_constant_with_view(p, r3, wraps.at(2));
    p.post(Table{{v1, v2, v3}, allowed});

    auto proof_name = proofs ? make_optional("table_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{v1, v2, v3});
    check_results(proof_name, expected, actual);
}

// Dup-variable test: Table with the same handle in several positions.
// Tuples where the duplicated positions disagree are infeasible.
// Consistency isn't checked on dup runs; see tmp/duplicate_var_audit.md.
auto run_dup_table_test(bool proofs, const vector<pair<int, int>> & unique_domains,
    const vector<int> & positions, SimpleTuples allowed) -> void
{
    print(cerr, "table dup unique_doms={} positions={} {} tuples{}",
        unique_domains, positions, allowed.size(), proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<vector<int>>> expected, actual;
    build_expected(
        expected, [&](const vector<int> & unique_vals) -> bool {
            for (const auto & t : allowed) {
                bool match = true;
                for (size_t i = 0; i < positions.size(); ++i)
                    if (t.at(i).raw_value != unique_vals.at(positions.at(i))) {
                        match = false;
                        break;
                    }
                if (match) return true;
            }
            return false;
        },
        unique_domains);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> unique_vars;
    for (const auto & d : unique_domains)
        unique_vars.push_back(p.create_integer_variable(Integer(d.first), Integer(d.second)));
    vector<IntegerVariableID> vars;
    for (auto pos : positions)
        vars.push_back(unique_vars.at(pos));
    p.post(Table{vars, allowed});

    auto proof_name = proofs ? make_optional("table_test_dup") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{unique_vars});
    check_results(proof_name, expected, actual);
}

auto run_all_tests(bool proofs, const ViewWrapConfig & view_cfg) -> void
{
    // Table, 2 variables
    run_table_test_2(proofs, view_cfg, {1, 3}, {1, 3},
        {{1_i, 1_i}, {1_i, 3_i}, {2_i, 2_i}, {3_i, 1_i}});
    run_table_test_2(proofs, view_cfg, {1, 4}, {1, 4},
        {{1_i, 2_i}, {2_i, 1_i}, {3_i, 4_i}, {4_i, 3_i}});
    run_table_test_2(proofs, view_cfg, {1, 3}, {1, 3},
        {});  // empty table: unsatisfiable
    run_table_test_2(proofs, view_cfg, {-2, 2}, {-2, 2},
        {{-2_i, 2_i}, {0_i, 0_i}, {2_i, -2_i}});
    // Degenerate (issue #254): all-fixed variables, both directions, and a
    // mixed fixed+variable case. (Empty tuple list → UNSAT is covered above.)
    run_table_test_2(proofs, view_cfg, {1, 1}, {1, 1},
        {{1_i, 1_i}});  // fixed (1,1) is an allowed tuple (tautology)
    run_table_test_2(proofs, view_cfg, {2, 2}, {3, 3},
        {{1_i, 1_i}});  // fixed (2,3) is not in the table (contradiction)
    run_table_test_2(proofs, view_cfg, {1, 1}, {1, 3},
        {{1_i, 1_i}, {1_i, 2_i}});  // mixed: v1 fixed, v2 variable

    // Table, 3 variables
    run_table_test_3(proofs, view_cfg, {1, 3}, {1, 3}, {1, 3},
        {{1_i, 1_i, 1_i}, {1_i, 2_i, 3_i}, {2_i, 1_i, 3_i}, {3_i, 3_i, 3_i}});
    run_table_test_3(proofs, view_cfg, {1, 3}, {2, 4}, {1, 2},
        {{2_i, 3_i, 1_i}, {2_i, 4_i, 2_i}});  // tight domain: forces propagation
    run_table_test_3(proofs, view_cfg, {1, 3}, {1, 3}, {1, 3},
        {});  // empty table: unsatisfiable
    run_table_test_3(proofs, view_cfg, {-2, 2}, {-2, 2}, {-2, 2},
        {{-2_i, 0_i, 2_i}, {0_i, 0_i, 0_i}, {2_i, 0_i, -2_i}});

    // Wildcard Table
    run_wildcard_table_test(proofs, view_cfg, {1, 3}, {1, 3}, {1, 3},
        {{{Wildcard{}, 2_i, Wildcard{}}}});  // only middle position must be 2
    run_wildcard_table_test(proofs, view_cfg, {1, 3}, {1, 3}, {1, 3},
        {{{1_i, Wildcard{}, 3_i}, {Wildcard{}, 2_i, Wildcard{}}}});
    run_wildcard_table_test(proofs, view_cfg, {1, 3}, {1, 3}, {1, 3},
        {{{Wildcard{}, Wildcard{}, Wildcard{}}}});  // all wildcards: all tuples allowed
}

auto main(int argc, char * argv[]) -> int
{
    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    constexpr int n_positions = 3;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "table view sweep: position {} out of range for n_positions = {}; skipping",
            *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    bool run_dup = view_wrap_config_is_effectively_bare(view_cfg, n_positions);

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        run_all_tests(proofs, view_cfg);
        if (run_dup) {
            // {x, y, x} with mixed-match tuples: (1, 2, 1) matches (cols 0
            // and 2 share x=1), (1, 2, 2) does not (cols 0 and 2 disagree).
            run_dup_table_test(proofs, {{1, 3}, {1, 3}}, {0, 1, 0},
                {{1_i, 2_i, 1_i}, {1_i, 2_i, 2_i}, {2_i, 3_i, 2_i}, {3_i, 3_i, 3_i}});
            // {x, x} — only diagonal tuples can match.
            run_dup_table_test(proofs, {{1, 3}}, {0, 0},
                {{1_i, 1_i}, {2_i, 3_i}, {3_i, 3_i}});
        }
    }

    return EXIT_SUCCESS;
}
