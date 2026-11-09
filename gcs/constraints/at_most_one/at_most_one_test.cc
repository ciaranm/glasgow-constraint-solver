#include <gcs/constraints/at_most_one.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
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
using std::mt19937;
using std::nullopt;
using std::pair;
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

enum class Variant
{
    Native,
    SmartTable
};

auto run_at_most_one_test(
    Variant variant, bool proofs, const ViewWrapConfig & view_cfg, const vector<pair<int, int>> & ranges, pair<int, int> val_range) -> void
{
    auto wraps = wraps_for_positions(view_cfg, static_cast<int>(ranges.size()));
    auto label = (variant == Variant::Native) ? "at_most_one" : "at_most_one_smart_table";
    print(cerr, "{} [{}] {} val={}{}", label, view_wrap_config_label(view_cfg), ranges, val_range, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<vector<int>, int>> expected, actual;
    build_expected(
        expected,
        [](const vector<int> & vs, int v) {
            int matches = 0;
            for (auto x : vs)
                matches += (x == v);
            return matches <= 1;
        },
        ranges, val_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> vars;
    for (std::size_t i = 0; i < ranges.size(); ++i)
        vars.push_back(create_integer_variable_or_constant_with_view(p, ranges[i], wraps.at(i)));
    auto val = p.create_integer_variable(Integer(val_range.first), Integer(val_range.second));
    if (variant == Variant::Native)
        p.post(AtMostOne{vars, val});
    else
        p.post(AtMostOneSmartTable{vars, val});

    auto proof_name = proofs ? make_optional("at_most_one_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{vars, val});
    check_results(proof_name, expected, actual);
}

// Dup-variable test: AtMostOne with the same handle in several array
// positions. {x, x, ...} forces x != val (otherwise two occurrences
// equal val). Consistency isn't checked on dup runs; see
// tmp/duplicate_var_audit.md.
auto run_dup_at_most_one_test(
    Variant variant, bool proofs, const vector<pair<int, int>> & unique_domains, const vector<int> & positions, pair<int, int> val_range) -> void
{
    auto label = (variant == Variant::Native) ? "at_most_one" : "at_most_one_smart_table";
    print(cerr, "{} dup domains={} positions={} val={}{}", label, unique_domains, positions, val_range, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<vector<int>, int>> expected, actual;
    build_expected(
        expected,
        [&](const vector<int> & vals, int v) -> bool {
            int matches = 0;
            for (auto pos : positions)
                if (vals.at(pos) == v)
                    ++matches;
            return matches <= 1;
        },
        unique_domains, val_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> unique_vars;
    for (const auto & d : unique_domains)
        unique_vars.push_back(p.create_integer_variable(Integer(d.first), Integer(d.second)));
    vector<IntegerVariableID> array;
    for (auto pos : positions)
        array.push_back(unique_vars.at(pos));
    auto val = p.create_integer_variable(Integer(val_range.first), Integer(val_range.second));
    if (variant == Variant::Native)
        p.post(AtMostOne{array, val});
    else
        p.post(AtMostOneSmartTable{array, val});

    auto proof_name = proofs ? make_optional(string{label} + "_test_dup") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{unique_vars, val});
    check_results(proof_name, expected, actual);
}

// One term of an AtMostOne: a constant, or sign * unique[var] + offset.
struct Term
{
    int var; // -1 for a constant, which is then the offset
    int sign = 1;
    int offset = 0;
};

auto term_value(const Term & t, const vector<int> & values) -> int
{
    return t.var < 0 ? t.offset : t.sign * values.at(t.var) + t.offset;
}

auto term_id(const Term & t, const vector<IntegerVariableID> & unique_vars) -> IntegerVariableID
{
    if (t.var < 0)
        return constant_variable(Integer(t.offset));
    if (t.sign > 0 && t.offset == 0)
        return unique_vars.at(t.var); // the same handle, so aliasing is real
    return t.sign > 0 ? unique_vars.at(t.var) + Integer(t.offset) : -unique_vars.at(t.var) + Integer(t.offset);
}

// val as a view, a constant, or a term over one of the positions' own
// variables: the cases where rule 2's val == v literal and the val trigger
// matter most. When val shares a variable with a position, the run checks
// solutions and the proof but not consistency, as for the dup runs.
auto run_val_kind_test(Variant variant, bool proofs, const string & what, const vector<pair<int, int>> & unique_domains,
    const vector<Term> & positions, const Term & val_term) -> void
{
    auto label = (variant == Variant::Native) ? "at_most_one" : "at_most_one_smart_table";
    print(cerr, "{} val kind {} domains={}{}", label, what, unique_domains, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<vector<int>>> expected, actual;
    build_expected(
        expected,
        [&](const vector<int> & values) -> bool {
            int v = term_value(val_term, values);
            int matches = 0;
            for (const auto & t : positions)
                matches += (term_value(t, values) == v);
            return matches <= 1;
        },
        unique_domains);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> unique_vars;
    for (const auto & d : unique_domains)
        unique_vars.push_back(p.create_integer_variable(Integer(d.first), Integer(d.second)));
    vector<IntegerVariableID> array;
    for (const auto & t : positions)
        array.push_back(term_id(t, unique_vars));
    auto val = term_id(val_term, unique_vars);
    if (variant == Variant::Native)
        p.post(AtMostOne{array, val});
    else
        p.post(AtMostOneSmartTable{array, val});

    bool aliased = false;
    for (const auto & t : positions)
        aliased = aliased || (val_term.var >= 0 && t.var == val_term.var);

    auto proof_name = proofs ? make_optional(string{label} + "_test_val_kind") : nullopt;
    if (aliased)
        solve_for_tests(p, proof_name, actual, tuple{unique_vars});
    else
        solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{unique_vars});
    check_results(proof_name, expected, actual);
}

auto run_val_kind_tests(Variant variant, bool proofs) -> void
{
    // Positions a, b, c and, where val needs one, its own variable d. Small
    // enough that every run stays under the default test caps, so each is
    // checked complete.
    vector<pair<int, int>> abc{{-1, 2}, {-1, 2}, {-1, 2}};
    vector<pair<int, int>> abcd{{-1, 2}, {-1, 2}, {-1, 2}, {0, 2}};
    vector<Term> plain{{0}, {1}, {2}};
    vector<Term> mixed{{0, 1, 1}, {1}, {2, -1, 0}}; // a + 1, b, -c

    run_val_kind_test(variant, proofs, "d + 1", abcd, plain, {3, 1, 1});
    run_val_kind_test(variant, proofs, "-d + 2", abcd, plain, {3, -1, 2});
    run_val_kind_test(variant, proofs, "-d + 2, mixed positions", abcd, mixed, {3, -1, 2});
    run_val_kind_test(variant, proofs, "constant 1", abc, plain, {-1, 1, 1});
    run_val_kind_test(variant, proofs, "constant 1, mixed positions", abc, mixed, {-1, 1, 1});
    // AtMostOneSmartTable refuses val among the positions, by design (see
    // at_most_one.md, "Variable kinds and views"), so these are native only.
    if (variant != Variant::Native)
        return;
    run_val_kind_test(variant, proofs, "a", abc, plain, {0});
    run_val_kind_test(variant, proofs, "-a", abc, plain, {0, -1, 0});
    run_val_kind_test(variant, proofs, "a + 1", abc, plain, {0, 1, 1});
    run_val_kind_test(variant, proofs, "a - 1", abc, plain, {0, 1, -1});
    run_val_kind_test(variant, proofs, "c, mixed positions", abc, mixed, {2});
}

auto run_all_tests(Variant variant, bool proofs, const ViewWrapConfig & view_cfg) -> void
{
    // Boundary: empty / singleton — both vacuously true.
    run_at_most_one_test(variant, proofs, view_cfg, {}, {1, 3});
    run_at_most_one_test(variant, proofs, view_cfg, {{1, 3}}, {1, 3});

    // Two vars: smallest meaningful case.
    run_at_most_one_test(variant, proofs, view_cfg, {{1, 3}, {1, 3}}, {2, 2});
    run_at_most_one_test(variant, proofs, view_cfg, {{1, 3}, {1, 3}}, {1, 3});

    // 3-variable tests, fixed val (single-point range)
    run_at_most_one_test(variant, proofs, view_cfg, {{1, 3}, {1, 3}, {1, 3}}, {2, 2});    // basic, val=2
    run_at_most_one_test(variant, proofs, view_cfg, {{1, 3}, {1, 3}, {1, 3}}, {5, 5});    // val outside all domains
    run_at_most_one_test(variant, proofs, view_cfg, {{1, 3}, {1, 3}, {1, 3}}, {1, 1});    // val at domain boundary
    run_at_most_one_test(variant, proofs, view_cfg, {{-2, 2}, {-2, 2}, {-2, 2}}, {0, 0}); // negative domain, val=0

    // 3-variable tests, variable val
    run_at_most_one_test(variant, proofs, view_cfg, {{1, 3}, {1, 3}, {1, 3}}, {1, 3});
    run_at_most_one_test(variant, proofs, view_cfg, {{1, 3}, {1, 3}, {1, 3}}, {2, 4});

    // Propagation: one var forced to equal val, others must differ
    run_at_most_one_test(variant, proofs, view_cfg, {{2, 2}, {1, 3}, {1, 3}}, {2, 2});
    run_at_most_one_test(variant, proofs, view_cfg, {{2, 2}, {2, 2}, {1, 3}}, {1, 3});

    // Unsatisfiable: two vars forced to equal a fixed val
    run_at_most_one_test(variant, proofs, view_cfg, {{2, 2}, {2, 2}, {1, 3}}, {2, 2});

    // Fully all-fixed (issue #254), both directions: every var and the value
    // are singletons, so the constraint reduces to a count check.
    run_at_most_one_test(variant, proofs, view_cfg, {{5, 5}, {5, 5}}, {5, 5}); // two equal val: contradiction
    run_at_most_one_test(variant, proofs, view_cfg, {{5, 5}, {6, 6}}, {5, 5}); // exactly one equals val: tautology
    run_at_most_one_test(variant, proofs, view_cfg, {{6, 6}, {7, 7}}, {5, 5}); // none equals val: tautology

    // 4-variable tests
    run_at_most_one_test(variant, proofs, view_cfg, {{1, 3}, {1, 3}, {1, 3}, {1, 3}}, {2, 2});
    run_at_most_one_test(variant, proofs, view_cfg, {{2, 2}, {1, 3}, {1, 3}, {1, 3}}, {2, 2});
    run_at_most_one_test(variant, proofs, view_cfg, {{1, 3}, {1, 3}, {1, 3}, {1, 3}}, {1, 3});
    run_at_most_one_test(variant, proofs, view_cfg, {{2, 2}, {2, 2}, {1, 3}, {1, 3}}, {1, 3});
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    constexpr int n_positions = 5;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "at_most_one view sweep: position {} out of range for n_positions = {}; skipping", *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    mt19937 rand(*get_seed());

    bool effectively_bare = view_wrap_config_is_effectively_bare(view_cfg, n_positions);
    bool run_dup = effectively_bare;

    for (auto variant : {Variant::Native, Variant::SmartTable}) {
        for (bool proofs : {false, true}) {
            if (proofs && ! can_run_veripb())
                continue;
            run_all_tests(variant, proofs, view_cfg);

            // Small random sweep: 2..5 vars, modest domains so the solution
            // space stays small. Solution count is O(|val| * prod(|vars|))
            // worst case, which on these bounds is at most ~5^5 = 3125 even
            // before the at-most-one filter, so VeriPB stays fast.
            uniform_int_distribution n_vars_dist{2, 5};
            uniform_int_distribution lo_dist{-2, 4};
            uniform_int_distribution width_dist{0, 4};
            for (int x = 0; x < 10; ++x) {
                int n_vars = n_vars_dist(rand);
                vector<pair<int, int>> ranges;
                for (int i = 0; i < n_vars; ++i) {
                    int lo = lo_dist(rand);
                    ranges.emplace_back(lo, lo + width_dist(rand));
                }
                int v_lo = lo_dist(rand);
                run_at_most_one_test(variant, proofs, view_cfg, ranges, {v_lo, v_lo + width_dist(rand)});
            }

            if (run_dup) {
                run_val_kind_tests(variant, proofs);

                // {x, x} — forces x != val.
                run_dup_at_most_one_test(variant, proofs, {{1, 3}}, {0, 0}, {1, 3});
                // {x, x, y} — x != val; y unconstrained by it.
                run_dup_at_most_one_test(variant, proofs, {{1, 3}, {1, 3}}, {0, 0, 1}, {2, 2});
                // {x, y, x} — same as above with reordering.
                run_dup_at_most_one_test(variant, proofs, {{1, 3}, {1, 3}}, {0, 1, 0}, {1, 3});
            }
        }
    }

    return EXIT_SUCCESS;
}
