#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/table/negative_table.hh>
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

auto run_negative_table_test_2(bool proofs, const ViewWrapConfig & view_cfg, pair<int, int> r1, pair<int, int> r2, SimpleTuples forbidden) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 2);
    print(cerr, "negative table 2var [{}] [{},{}] [{},{}] {} tuples{}", view_wrap_config_label(view_cfg), r1.first, r1.second, r2.first, r2.second,
        forbidden.size(), proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, int>> expected, actual;
    build_expected(
        expected,
        [&](int a, int b) -> bool {
            for (const auto & t : forbidden)
                if (t[0].raw_value == a && t[1].raw_value == b)
                    return false;
            return true;
        },
        r1, r2);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = create_integer_variable_or_constant_with_view(p, r1, wraps.at(0));
    auto v2 = create_integer_variable_or_constant_with_view(p, r2, wraps.at(1));
    p.post(NegativeTable{{v1, v2}, forbidden});

    auto proof_name = proofs ? make_optional("negative_table_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{v1, v2});
    check_results(proof_name, expected, actual);
}

auto run_negative_table_test_3(
    bool proofs, const ViewWrapConfig & view_cfg, pair<int, int> r1, pair<int, int> r2, pair<int, int> r3, SimpleTuples forbidden) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 3);
    print(cerr, "negative table 3var [{}] [{},{}] [{},{}] [{},{}] {} tuples{}", view_wrap_config_label(view_cfg), r1.first, r1.second, r2.first,
        r2.second, r3.first, r3.second, forbidden.size(), proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, int, int>> expected, actual;
    build_expected(
        expected,
        [&](int a, int b, int c) -> bool {
            for (const auto & t : forbidden)
                if (t[0].raw_value == a && t[1].raw_value == b && t[2].raw_value == c)
                    return false;
            return true;
        },
        r1, r2, r3);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = create_integer_variable_or_constant_with_view(p, r1, wraps.at(0));
    auto v2 = create_integer_variable_or_constant_with_view(p, r2, wraps.at(1));
    auto v3 = create_integer_variable_or_constant_with_view(p, r3, wraps.at(2));
    p.post(NegativeTable{{v1, v2, v3}, forbidden});

    auto proof_name = proofs ? make_optional("negative_table_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{v1, v2, v3});
    check_results(proof_name, expected, actual);
}

auto run_negative_wildcard_table_test(
    bool proofs, const ViewWrapConfig & view_cfg, pair<int, int> r1, pair<int, int> r2, pair<int, int> r3, WildcardTuples forbidden) -> void
{
    auto wraps = wraps_for_positions(view_cfg, 3);
    print(cerr, "negative wildcard table [{}] [{},{}] [{},{}] [{},{}] {} tuples{}", view_wrap_config_label(view_cfg), r1.first, r1.second, r2.first,
        r2.second, r3.first, r3.second, forbidden.size(), proofs ? " with proofs:" : ":");
    cerr << flush;

    auto entry_matches = [](const IntegerOrWildcard & entry, int val) -> bool {
        return overloaded{
            [val](Integer i) { return i.raw_value == val; }, //
            [](Wildcard) { return true; }                    //
        }
            .visit(entry);
    };

    set<tuple<int, int, int>> expected, actual;
    build_expected(
        expected,
        [&](int a, int b, int c) -> bool {
            for (const auto & t : forbidden)
                if (entry_matches(t[0], a) && entry_matches(t[1], b) && entry_matches(t[2], c))
                    return false;
            return true;
        },
        r1, r2, r3);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto v1 = create_integer_variable_or_constant_with_view(p, r1, wraps.at(0));
    auto v2 = create_integer_variable_or_constant_with_view(p, r2, wraps.at(1));
    auto v3 = create_integer_variable_or_constant_with_view(p, r3, wraps.at(2));
    p.post(NegativeTable{{v1, v2, v3}, forbidden});

    auto proof_name = proofs ? make_optional("negative_table_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{v1, v2, v3});
    check_results(proof_name, expected, actual);
}

// Dup-variable test: NegativeTable with the same handle in several
// positions. Forbidden tuples whose dup positions disagree are
// vacuously satisfied (the underlying assignment is impossible).
// Consistency isn't checked on dup runs; see tmp/duplicate_var_audit.md.
auto run_dup_negative_table_test(bool proofs, const vector<pair<int, int>> & unique_domains, const vector<int> & positions, SimpleTuples forbidden)
    -> void
{
    print(cerr, "negative table dup unique_doms={} positions={} {} tuples{}", unique_domains, positions, forbidden.size(),
        proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<vector<int>>> expected, actual;
    build_expected(
        expected,
        [&](const vector<int> & unique_vals) -> bool {
            for (const auto & t : forbidden) {
                bool match = true;
                for (size_t i = 0; i < positions.size(); ++i)
                    if (t.at(i).raw_value != unique_vals.at(positions.at(i))) {
                        match = false;
                        break;
                    }
                if (match)
                    return false;
            }
            return true;
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
    p.post(NegativeTable{vars, forbidden});

    auto proof_name = proofs ? make_optional("negative_table_test_dup") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{unique_vars});
    check_results(proof_name, expected, actual);
}

auto run_all_tests(bool proofs, const ViewWrapConfig & view_cfg) -> void
{
    // Two-variable cases.
    run_negative_table_test_2(proofs, view_cfg, {1, 3}, {1, 3}, {{1_i, 1_i}});                                     // single forbidden
    run_negative_table_test_2(proofs, view_cfg, {1, 3}, {1, 3}, {{1_i, 1_i}, {2_i, 2_i}, {3_i, 3_i}});             // exclude diagonal
    run_negative_table_test_2(proofs, view_cfg, {1, 2}, {1, 2}, {{1_i, 1_i}, {1_i, 2_i}, {2_i, 1_i}, {2_i, 2_i}}); // all forbidden: unsat at root
    run_negative_table_test_2(proofs, view_cfg, {1, 3}, {2, 2}, {{1_i, 2_i}}); // singleton domain forces v1!=1 at root (unit at init)
    run_negative_table_test_2(
        proofs, view_cfg, {1, 3}, {1, 3}, {{4_i, 4_i}, {1_i, 1_i}}); // first tuple already infeasible (4 not in dom): satisfied automatically
    run_negative_table_test_2(proofs, view_cfg, {1, 3}, {1, 3}, {{1_i, 1_i}, {1_i, 1_i}, {2_i, 2_i}}); // duplicates in forbidden list
    // Degenerate (issue #254): empty forbidden list (all allowed) and all-fixed
    // variables in both directions.
    run_negative_table_test_2(proofs, view_cfg, {1, 3}, {1, 3}, {});                       // empty forbidden list: every assignment allowed
    run_negative_table_test_2(proofs, view_cfg, {1, 1}, {2, 2}, {{2_i, 1_i}, {3_i, 3_i}}); // fixed (1,2) not forbidden (tautology)
    run_negative_table_test_2(proofs, view_cfg, {1, 1}, {2, 2}, {{1_i, 2_i}});             // fixed (1,2) is forbidden (contradiction)

    // Three-variable cases.
    run_negative_table_test_3(proofs, view_cfg, {1, 3}, {1, 3}, {1, 3}, {{1_i, 1_i, 1_i}, {2_i, 2_i, 2_i}, {3_i, 3_i, 3_i}}); // exclude diagonal
    run_negative_table_test_3(proofs, view_cfg, {1, 2}, {1, 2}, {1, 2},
        {{1_i, 1_i, 1_i}, {1_i, 1_i, 2_i}, {1_i, 2_i, 1_i}, {1_i, 2_i, 2_i},      //
            {2_i, 1_i, 1_i}, {2_i, 1_i, 2_i}, {2_i, 2_i, 1_i}, {2_i, 2_i, 2_i}}); // all forbidden: unsat
    run_negative_table_test_3(proofs, view_cfg, {1, 3}, {2, 4}, {1, 2}, {{1_i, 2_i, 1_i}, {3_i, 4_i, 2_i}});
    run_negative_table_test_3(proofs, view_cfg, {1, 3}, {1, 3}, {1, 3},
        {{1_i, 1_i, 1_i}, {1_i, 1_i, 2_i}, {1_i, 1_i, 3_i}}); // (1,1,*) all forbidden: forces v1!=1 OR v2!=1 (cascade)
    run_negative_table_test_3(proofs, view_cfg, {-2, 2}, {-2, 2}, {-2, 2}, {{-2_i, 0_i, 2_i}, {0_i, 0_i, 0_i}, {2_i, 0_i, -2_i}});

    // Larger forbidden tables to exercise watched-literal scaling.
    run_negative_table_test_3(proofs, view_cfg, {1, 4}, {1, 4}, {1, 4},
        {{1_i, 1_i, 1_i}, {1_i, 2_i, 3_i}, {2_i, 1_i, 4_i}, {2_i, 3_i, 2_i},    //
            {3_i, 4_i, 1_i}, {4_i, 2_i, 3_i}, {4_i, 4_i, 4_i}, {1_i, 3_i, 2_i}, //
            {2_i, 2_i, 2_i}, {3_i, 3_i, 3_i}});

    // Wildcard cases.
    run_negative_wildcard_table_test(proofs, view_cfg, {1, 3}, {1, 3}, {1, 3}, {{{Wildcard{}, 2_i, Wildcard{}}}}); // forbid all tuples with v2=2
    run_negative_wildcard_table_test(
        proofs, view_cfg, {1, 3}, {1, 3}, {1, 3}, {{{1_i, Wildcard{}, 3_i}, {2_i, 2_i, Wildcard{}}}}); // mixed wildcard forbids
    run_negative_wildcard_table_test(
        proofs, view_cfg, {1, 3}, {1, 3}, {1, 3}, {{{Wildcard{}, Wildcard{}, Wildcard{}}}}); // all-wildcard tuple: unsat at root
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    constexpr int n_positions = 3;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "negative_table view sweep: position {} out of range for n_positions = {}; skipping", *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    bool run_dup = view_wrap_config_is_effectively_bare(view_cfg, n_positions);

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        run_all_tests(proofs, view_cfg);
        if (run_dup) {
            // {x, y, x} — a forbidden tuple (1, 2, 1) forbids x=1,y=2; tuple
            // (1, 2, 3) is vacuously satisfied (x can't be both 1 and 3).
            run_dup_negative_table_test(proofs, {{1, 3}, {1, 3}}, {0, 1, 0}, {{1_i, 2_i, 1_i}, {1_i, 2_i, 3_i}, {2_i, 3_i, 2_i}});
            // {x, x} — only diagonal tuples actually forbid anything.
            run_dup_negative_table_test(proofs, {{1, 3}}, {0, 0}, {{1_i, 1_i}, {2_i, 3_i}});
        }
    }

    return EXIT_SUCCESS;
}
