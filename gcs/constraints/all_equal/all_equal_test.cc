#include <gcs/constraints/all_equal.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/in.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <functional>
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
using std::function;
using std::make_optional;
using std::make_pair;
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

// A removed interval whose parts are missing from *different* variables.
//
// The intersection pruning takes each variable's domain minus the intersection of
// all of them, so a single contiguous run of that difference can be explained by
// one variable at its start and another at its end. That is the case the reason
// has to split by witness, and nothing else in this file reaches it: everywhere
// else, one variable's hole happens to cover the whole run.
//
// x is the full range; y is missing the lower half of the middle band and z the
// upper half, so the band leaves x as one interval that neither alone witnesses.
//
// Bare variables only, like run_holes_test above, and gated the same way. The view
// lanes would add nothing here -- nothing is wrapped -- but they would share this
// fixed proof basename with the plain lane, and the two lanes share a working
// directory and delete their proofs once veripb has run. Under `ctest -j` that
// races: 5 rounds in 6 of `ctest -R all_equal -j 8` failed before the gate, either
// losing the file outright or parsing one still being written.
auto run_mixed_witness_test(bool proofs) -> void
{
    print(cerr, "all_equal mixed witness{}", proofs ? " with proofs:" : ":");
    cerr << flush;

    const int hi = 20;
    auto without = [](int lo, int upper, int gap_lo, int gap_hi) {
        vector<int> vs;
        for (int v = lo; v <= upper; ++v)
            if (v < gap_lo || v > gap_hi)
                vs.push_back(v);
        return vs;
    };
    auto dy = without(0, hi, 5, 9);
    auto dz = without(0, hi, 10, 14);

    auto in = [](int v, const vector<int> & sv) {
        for (auto u : sv)
            if (u == v)
                return true;
        return false;
    };

    set<tuple<int, int, int>> expected, actual;
    build_expected(
        expected, [&](int x, int y, int z) -> bool { return x == y && y == z && in(y, dy) && in(z, dz); }, pair{0, hi}, pair{0, hi}, pair{0, hi});
    println(cerr, " expecting {} solutions", expected.size());

    auto to_integers = [](const vector<int> & vs) {
        vector<Integer> out;
        for (auto v : vs)
            out.emplace_back(v);
        return out;
    };

    Problem p;
    auto x = p.create_integer_variable(0_i, Integer{hi});
    auto y = p.create_integer_variable(to_integers(dy));
    auto z = p.create_integer_variable(to_integers(dz));
    p.post(AllEqual{vector<IntegerVariableID>{x, y, z}});

    auto proof_name = proofs ? make_optional("all_equal_test_mixed_witness") : nullopt;
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

// Issue #1153 shapes. Each underlying variable has a listed domain, and each
// position of the AllEqual is `sign * var + offset` over one of them, so a
// variable can be repeated plainly or through a view, and an underlying
// variable no position mentions is free. The expected set is brute-forced over
// the underlying variables.
struct Position
{
    int var;
    int sign;
    int offset;
};

auto int_range(int lo, int hi) -> vector<int>
{
    vector<int> result;
    for (int v = lo; v <= hi; ++v)
        result.push_back(v);
    return result;
}

auto to_integers(const vector<int> & vs) -> vector<Integer>
{
    vector<Integer> result;
    for (auto v : vs)
        result.emplace_back(v);
    return result;
}

auto enumerate_assignments(const vector<vector<int>> & domains, const function<bool(const vector<int> &)> & is_satisfying) -> set<tuple<vector<int>>>
{
    set<tuple<vector<int>>> result;
    vector<int> values(domains.size());
    function<void(size_t)> rec = [&](size_t i) {
        if (i == domains.size()) {
            if (is_satisfying(values))
                result.emplace(values);
            return;
        }
        for (auto v : domains[i]) {
            values[i] = v;
            rec(i + 1);
        }
    };
    rec(0);
    return result;
}

auto position_value(const Position & pos, const vector<int> & values) -> int
{
    return pos.sign * values.at(pos.var) + pos.offset;
}

auto position_variable(const Position & pos, const vector<IntegerVariableID> & vars) -> IntegerVariableID
{
    auto v = vars.at(pos.var);
    if (pos.sign == 1)
        return v + Integer(pos.offset);
    return -v + Integer(pos.offset);
}

// The propagator used to disable itself whenever vars[0] was single-valued
// after a call, but either of its passes can fix vars[0] part-way through
// while another position still holds a different value, or several. Every
// shape the call site in main() passes here gave wrong answers that way,
// except {x, x + 1} at an odd width: there the domain empties before x is
// fixed, so that one is a control that passed on the old code too.
auto run_disable_test(bool proofs, const string & label, const vector<vector<int>> & domains, const vector<Position> & positions, bool check_gac)
    -> void
{
    print(cerr, "all_equal disable [{}]{}", label, proofs ? " with proofs:" : ":");
    cerr << flush;

    auto expected = enumerate_assignments(domains, [&](const vector<int> & values) {
        for (const auto & pos : positions)
            if (position_value(pos, values) != position_value(positions.at(0), values))
                return false;
        return true;
    });
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> vars;
    for (const auto & d : domains)
        vars.push_back(p.create_integer_variable(to_integers(d)));
    vector<IntegerVariableID> posted;
    for (const auto & pos : positions)
        posted.push_back(position_variable(pos, vars));
    p.post(AllEqual{posted});

    set<tuple<vector<int>>> actual;
    auto proof_name = proofs ? make_optional("all_equal_test_disable") : nullopt;
    if (check_gac)
        solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{vars});
    else
        solve_for_tests(p, proof_name, actual, tuple{vars});
    check_results(proof_name, expected, actual);
}

// The same bug with holes made during search rather than at the root: other
// constraints punch holes and move bounds, under a fixed branching order that
// is known to reach it. The harness's random branching might not, so this one
// solves with its own. Each instance came from a random search over models of
// this shape (the first two) or is the MiniZinc model in
// minizinc/tests/allequalsearchholes.mzn (the third).
auto run_search_holes_test(bool proofs, const string & label, const vector<pair<int, int>> & domains, const vector<pair<int, int>> & not_equals,
    const vector<tuple<int, int, int>> & sum_at_most, const vector<int> & all_equal, const vector<int> & branch_order) -> void
{
    print(cerr, "all_equal search holes [{}]{}", label, proofs ? " with proofs:" : ":");
    cerr << flush;

    vector<vector<int>> listed;
    for (auto [lo, hi] : domains)
        listed.push_back(int_range(lo, hi));
    auto expected = enumerate_assignments(listed, [&](const vector<int> & values) {
        for (auto i : all_equal)
            if (values.at(i) != values.at(all_equal.at(0)))
                return false;
        for (auto [i, j] : not_equals)
            if (values.at(i) == values.at(j))
                return false;
        for (auto [i, j, c] : sum_at_most)
            if (values.at(i) + values.at(j) > c)
                return false;
        return true;
    });
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> vars;
    for (auto [lo, hi] : domains)
        vars.push_back(p.create_integer_variable(Integer(lo), Integer(hi)));
    for (auto [i, j] : not_equals)
        p.post(NotEquals{vars.at(i), vars.at(j)});
    for (auto [i, j, c] : sum_at_most)
        p.post(LinearLessThanEqual{WeightedSum{} + 1_i * vars.at(i) + 1_i * vars.at(j), Integer(c)});
    vector<IntegerVariableID> posted;
    for (auto i : all_equal)
        posted.push_back(vars.at(i));
    p.post(AllEqual{posted});
    vector<IntegerVariableID> branch_vars;
    for (auto i : branch_order)
        branch_vars.push_back(vars.at(i));

    set<tuple<vector<int>>> actual;
    auto proof_name = proofs ? make_optional("all_equal_test_search_holes") : nullopt;
    last_run_truncated() = false;
    solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool { return actual.emplace(extract_from_state(s, vars)), true; }, //
            .branch = branch_with(variable_order::in_order(branch_vars), value_order::smallest_first()),                   //
            .stats_report = silent_stats_report()                                                                          //
        },
        proof_name ? make_optional<ProofOptions>(ProofFileNames{*proof_name}) : nullopt);
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
        if (run_holes) {
            run_holes_test(proofs);
            run_mixed_witness_test(proofs);
        }
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
            // Issue #1153. vars[0] holey, and no hole left once the bounds
            // pass is done, so the hole pass never runs: x in {1, 3} and
            // y in {2, 4} land on x = 3 and y = 2.
            run_disable_test(proofs, "holey_first_unsat", {{1, 3}, {2, 4}}, {{0, 1, 0}, {1, 1, 0}}, true);
            run_disable_test(proofs, "holey_first_sat", {{1, 5}, int_range(0, 3)}, {{0, 1, 0}, {1, 1, 0}}, true);
            run_disable_test(proofs, "holey_first_three", {{0, 2, 4}, int_range(1, 3), int_range(1, 3)}, {{0, 1, 0}, {1, 1, 0}, {2, 1, 0}}, true);
            // A repeat through an offset view fixes x part-way through the
            // bounds pass, over intervals; and through the hole pass's removals
            // from x + 1, when the bounds pass leaves x holey.
            run_disable_test(proofs, "offset_repeat", {int_range(0, 2), int_range(0, 5)}, {{0, 1, 0}, {1, 1, 0}, {0, 1, 1}}, false);
            run_disable_test(proofs, "offset_repeat_holey", {{-1, 0, 1, 2, 4, 5}, int_range(0, 5)}, {{0, 1, 0}, {1, 1, 0}, {0, 1, 1}}, false);
            // Through an opposite-sign view: 2 - x >= 1 fixes x = 1.
            run_disable_test(proofs, "negated_repeat", {int_range(0, 3), int_range(1, 5)}, {{0, 1, 0}, {1, 1, 0}, {0, -1, 2}}, false);
            // {x, x + 1} is unsatisfiable, and y is free. At an even width x is
            // fixed mid-call before its domain empties; at an odd width it
            // empties first.
            for (int width : {2, 10, 11})
                run_disable_test(
                    proofs, "offset_pair_width_" + std::to_string(width), {int_range(0, width), int_range(0, width)}, {{0, 1, 0}, {0, 1, 1}}, false);

            run_search_holes_test(proofs, "trial_437", {{1, 5}, {0, 3}, {0, 3}, {0, 5}, {0, 5}, {0, 5}}, {{0, 4}}, {{1, 4, 4}, {1, 4, 6}}, {0, 1, 2},
                {3, 4, 5, 0, 1, 2});
            run_search_holes_test(
                proofs, "trial_933", {{0, 3}, {1, 4}, {0, 4}, {0, 5}}, {{2, 3}, {2, 3}, {1, 3}}, {{0, 3, 4}}, {1, 0, 2}, {3, 0, 1, 2});
            run_search_holes_test(proofs, "minizinc", {{1, 5}, {0, 4}, {0, 5}}, {{1, 2}}, {{0, 2, 4}, {1, 2, 7}}, {1, 0}, {2, 0, 1});
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
