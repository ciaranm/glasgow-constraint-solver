#include <gcs/constraints/global_cardinality.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <optional>
#include <random>
#include <set>
#include <tuple>
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
using std::count;
using std::find;
using std::flush;
using std::make_optional;
using std::mt19937;
using std::nullopt;
using std::pair;
using std::set;
using std::tuple;
using std::uniform_int_distribution;
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

// A test variable is a constant, a lo/hi interval, or an explicit list of
// values -- the third shape being the only one that gives a variable holes,
// which is what the closed propagator's domain-difference needs to be run
// against (#877).
using Range = variant<int, pair<int, int>, vector<int>>;

auto run_bgcc_test(bool proofs, const vector<Range> & vars_range, const vector<int> & values, const vector<Range> & counts_range, bool closed) -> void
{
    print(cerr, "bgcc vars={} values={} counts={} closed={}{}", vars_range, values, counts_range, closed, proofs ? " with proofs:" : ":");
    cerr << flush;

    auto is_satisfying = [&](const vector<int> & vars, const vector<int> & counts) -> bool {
        for (std::size_t i = 0; i < values.size(); ++i)
            if (counts.at(i) != static_cast<int>(count(vars.begin(), vars.end(), values.at(i))))
                return false;
        if (closed)
            for (auto & v : vars)
                if (find(values.begin(), values.end(), v) == values.end())
                    return false;
        return true;
    };

    set<tuple<vector<int>, vector<int>>> expected, actual;
    build_expected(expected, is_satisfying, vars_range, counts_range);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> vars;
    for (const auto & r : vars_range)
        vars.push_back(visit([&](auto x) { return create_integer_variable_or_constant(p, x); }, r));
    vector<IntegerVariableID> counts;
    for (const auto & r : counts_range)
        counts.push_back(visit([&](auto x) { return create_integer_variable_or_constant(p, x); }, r));
    vector<Integer> int_values;
    for (auto & v : values)
        int_values.emplace_back(v);

    p.post(GlobalCardinality{vars, int_values, counts}.with_consistency(consistency::BC{}).with_closed(closed));

    // This dedicated propagator claims bounds consistency on both the
    // assignment variables and the count variables.
    auto proof_name = proofs ? make_optional("bounds_global_cardinality_test") : nullopt;
    solve_for_tests_checking_consistency(
        p, proof_name, expected, actual, tuple{pair{vars, CheckConsistency::BC}, pair{counts, CheckConsistency::BC}});
    check_results(proof_name, expected, actual);
}

// A variable and a view of it in the array (issue #1191). The Hall removals'
// reasons used to be built after the removal had been pushed, and with a view
// in the array that push moves another position's domain too, so the reason
// could come out naming the removal itself and justify nothing: VeriPB
// rejected the proof. The solutions were right. Positions are
// `+-under[base] + offset`; the solutions are checked over the underlying
// variables and the counts.
struct AliasedPosition
{
    std::size_t base;
    bool negate;
    int offset;
};

auto run_aliased_views_test(bool proofs, const vector<pair<int, int>> & under_ranges, const vector<AliasedPosition> & positions,
    const vector<int> & values, const vector<pair<int, int>> & counts_range, bool closed) -> void
{
    print(cerr, "bgcc aliased views under={} positions=[", under_ranges);
    for (const auto & q : positions)
        print(cerr, " {}u{}{:+}", q.negate ? "-" : "", q.base, q.offset);
    print(cerr, " ] values={} counts={} closed={}{}", values, counts_range, closed, proofs ? " with proofs:" : ":");
    cerr << flush;

    auto value_of = [&](const AliasedPosition & q, const vector<int> & under) { return (q.negate ? -under[q.base] : under[q.base]) + q.offset; };
    auto is_satisfying = [&](const vector<int> & under, const vector<int> & counts) -> bool {
        for (std::size_t j = 0; j < values.size(); ++j) {
            int c = 0;
            for (const auto & q : positions)
                if (value_of(q, under) == values[j])
                    ++c;
            if (c != counts[j])
                return false;
        }
        if (closed)
            for (const auto & q : positions)
                if (find(values.begin(), values.end(), value_of(q, under)) == values.end())
                    return false;
        return true;
    };

    set<tuple<vector<int>, vector<int>>> expected, actual;
    build_expected(expected, is_satisfying, under_ranges, counts_range);
    println(cerr, " expecting {} solutions", expected.size());

    auto post = [&](Problem & p) -> pair<vector<IntegerVariableID>, vector<IntegerVariableID>> {
        vector<IntegerVariableID> under, vars, counts;
        for (const auto & [lo, hi] : under_ranges)
            under.push_back(p.create_integer_variable(Integer(lo), Integer(hi)));
        for (const auto & q : positions)
            vars.push_back(q.negate ? -under[q.base] + Integer(q.offset) : under[q.base] + Integer(q.offset));
        for (const auto & [lo, hi] : counts_range)
            counts.push_back(p.create_integer_variable(Integer(lo), Integer(hi)));
        vector<Integer> int_values;
        for (auto v : values)
            int_values.emplace_back(v);
        p.post(GlobalCardinality{vars, int_values, counts}.with_closed(closed));
        return pair{under, counts};
    };

    auto proof_name = proofs ? make_optional("bgcc_aliased_views_test") : nullopt;
    {
        Problem p;
        auto [under, counts] = post(p);
        solve_for_tests(p, proof_name, actual, tuple{under, counts});
        check_results(proof_name, expected, actual);
    }

    // Again under the solver's default branching. The harness branches at
    // random, and the issue's instance needs the default order's path to reach
    // the removal whose reason went wrong.
    {
        Problem p;
        auto [under, counts] = post(p);
        actual.clear();
        last_run_truncated() = false;
        solve_with(p,
            SolveCallbacks{
                .solution = [&](const CurrentState & s) -> bool {
                    return actual.emplace(extract_from_state(s, under), extract_from_state(s, counts)), true;
                },                                    //
                .stats_report = silent_stats_report() //
            },
            proof_name ? make_optional<ProofOptions>(ProofFileNames{*proof_name}) : nullopt);
        check_results(proof_name, expected, actual);
    }
}

// The magic sequence, GlobalCardinality{x, {0, ..., n - 1}, x}: every count is
// one of the variables (issue #1191). The Hall pols read the counts' bounds, and
// the single-literal inference used to run them after its own push, so when
// the pushed variable was a count, the pol cited the new bound while the reason
// stated the old one. Proofs were rejected for several n on the bounds arm, from
// MiniZinc as well. Solved under the harness's random branching and under the
// default one.
auto run_magic_sequence_test(bool proofs, int n, bool closed) -> void
{
    print(cerr, "bgcc magic sequence n={} closed={}{}", n, closed, proofs ? " with proofs:" : ":");
    cerr << flush;

    auto is_satisfying = [&](const vector<int> & x) -> bool {
        for (int v = 0; v < n; ++v)
            if (count(x.begin(), x.end(), v) != x[v])
                return false;
        return true;
    };
    set<tuple<vector<int>>> expected, actual;
    build_expected(expected, is_satisfying, vector<pair<int, int>>(n, pair{0, n - 1}));
    println(cerr, " expecting {} solutions", expected.size());

    auto post = [&](Problem & p) -> vector<IntegerVariableID> {
        vector<IntegerVariableID> x;
        vector<Integer> values;
        for (int v = 0; v < n; ++v) {
            x.push_back(p.create_integer_variable(0_i, Integer(n - 1)));
            values.emplace_back(v);
        }
        p.post(GlobalCardinality{x, values, x}.with_closed(closed));
        return x;
    };

    auto proof_name = proofs ? make_optional("bgcc_magic_sequence_test") : nullopt;
    {
        Problem p;
        auto x = post(p);
        solve_for_tests(p, proof_name, actual, tuple{x});
        check_results(proof_name, expected, actual);
    }
    {
        Problem p;
        auto x = post(p);
        actual.clear();
        last_run_truncated() = false;
        solve_with(p,
            SolveCallbacks{
                .solution = [&](const CurrentState & s) -> bool { return actual.emplace(extract_from_state(s, x)), true; }, //
                .stats_report = silent_stats_report()                                                                       //
            },
            proof_name ? make_optional<ProofOptions>(ProofFileNames{*proof_name}) : nullopt);
        check_results(proof_name, expected, actual);
    }
}

// The issue's instance, with y + 3 and with 3 - y, and then seeded random
// positions over two underlying variables, each one plain, offset or negated,
// so that most instances put a variable and a view of it together. Its own
// generator, so that main's random instances stay what they were.
auto aliased_views_data() -> vector<tuple<vector<pair<int, int>>, vector<AliasedPosition>, vector<int>, vector<pair<int, int>>, bool>>
{
    mt19937 rand(*get_seed());
    vector<tuple<vector<pair<int, int>>, vector<AliasedPosition>, vector<int>, vector<pair<int, int>>, bool>> aliased_data = {
        {{{0, 4}, {-1, 2}}, {{0, false, 0}, {1, false, 0}, {1, false, 3}}, {0, 2}, {{0, 2}, {0, 2}}, false},
        {{{0, 4}, {-1, 2}}, {{0, false, 0}, {1, false, 0}, {1, true, 3}}, {0, 2}, {{0, 2}, {0, 2}}, false},
    };
    for (int iteration = 0; iteration < 16; ++iteration) {
        uniform_int_distribution lo_dist(-1, 1);
        uniform_int_distribution width_dist(1, 3);
        uniform_int_distribution n_positions_dist(3, 4);
        uniform_int_distribution base_dist(0, 1);
        uniform_int_distribution negate_dist(0, 2);
        uniform_int_distribution offset_dist(-2, 3);
        uniform_int_distribution n_values_dist(2, 3);
        uniform_int_distribution value_dist(-1, 4);
        uniform_int_distribution closed_dist(0, 1);

        vector<pair<int, int>> under_ranges;
        for (int u = 0; u < 2; ++u) {
            auto lo = lo_dist(rand);
            under_ranges.emplace_back(lo, lo + width_dist(rand));
        }
        vector<AliasedPosition> positions;
        auto n_positions = n_positions_dist(rand);
        for (int i = 0; i < n_positions; ++i) {
            bool negate = negate_dist(rand) == 0;
            positions.push_back(AliasedPosition{static_cast<std::size_t>(base_dist(rand)), negate, offset_dist(rand) + (negate ? 2 : 0)});
        }
        auto n_values = n_values_dist(rand);
        set<int> value_set;
        while (static_cast<int>(value_set.size()) < n_values)
            value_set.insert(value_dist(rand));
        vector<int> values(value_set.begin(), value_set.end());
        vector<pair<int, int>> counts_range(values.size(), pair{0, n_positions});
        aliased_data.emplace_back(under_ranges, positions, values, counts_range, closed_dist(rand) == 1);
    }

    return aliased_data;
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    vector<tuple<vector<Range>, vector<int>, vector<Range>, bool>> data = {
        // Upper-capacity Hall isolated: counts pinned and the fourth variable's
        // escape value (4) is outside the cover, so ONLY the multi-value removal
        // fires. First three confined to {1,2} with fixed capacity 2+1 force the
        // fourth off value 1.
        {{pair{1, 2}, pair{1, 2}, pair{1, 2}, pair{1, 4}}, {1, 2}, {2, 1}, false},
        // The same shape with the cover values spread apart, which is what makes
        // the capacity reason's "confined to the hall set" a real *range* rather
        // than a run of one (#936). The three confined variables take 1 or 5 and
        // nothing between, so the reason states that as ~[v in 2..4]; with the
        // cover at {1, 2} every run is a single value and `not_in_range`
        // canonicalises back to the disequality the per-value spelling emitted,
        // so the rows above this one reach the interval form only incidentally,
        // if at all --- which of them do depends on the seed. This row makes it
        // deterministic: every run emits `[2,4]`, which is what a regression test
        // for the interval spelling has to be.
        {{vector<int>{1, 5}, vector<int>{1, 5}, vector<int>{1, 5}, pair{1, 7}}, {1, 5}, {2, 1}, false},
        // Upper-capacity Hall: first three confined to {1,2} with capacity 2+1,
        // so the fourth variable is forced off value 1.
        {{pair{1, 2}, pair{1, 2}, pair{1, 2}, pair{1, 3}}, {1, 2, 3}, {pair{0, 2}, pair{0, 1}, pair{0, 3}}, false},
        // Lower-demand Hall: value 1 demanded at least twice, only two vars can
        // supply it, so both are forced to 1.
        {{pair{1, 4}, pair{1, 4}, pair{2, 5}}, {1, 2}, {pair{2, 3}, pair{0, 3}}, false},
        // Lower-demand Hall isolated: counts pinned to 1+1, two vars range over
        // 1..5; the demand of 2 over {1,2} exactly matches the two potential
        // suppliers (no single value forces), so ONLY the multi-value force
        // fires, removing 3,4,5 from both.
        {{pair{1, 5}, pair{1, 5}}, {1, 2}, {1, 1}, false},
        // Infeasible by capacity.
        {{pair{1, 2}, pair{1, 2}, pair{1, 2}}, {1, 2}, {pair{0, 1}, pair{0, 1}}, false},
        // Open, exact counts.
        {{pair{1, 2}, pair{1, 2}}, {1, 2}, {pair{0, 2}, pair{0, 2}}, false},
        // Closed.
        {{pair{1, 3}, pair{1, 3}, pair{2, 3}}, {1, 2, 3}, {pair{0, 3}, pair{0, 3}, pair{0, 3}}, true},
        // Closed over a domain with a hole in it (#877). The closed propagator
        // removes each run of non-cover values in one go, and the runs it has to
        // find are bounded by three different things at once here: the first
        // ends where the domain's own hole starts (0, then 2 is missing), the
        // second starts after a cover value inside an interval (3 covered, so
        // 4..5 is what is left of [3,5]). Nothing else posts a variable with a
        // hole in it under with_closed, so before this row every domain reaching
        // that propagator was one contiguous interval, and the case where
        // "group consecutive values" and "subtract one interval set from
        // another" could disagree was untested. The second variable is the same
        // instance without the hole, so the pair says the hole is what differs.
        {{vector<int>{0, 1, 3, 4, 5}, pair{0, 5}}, {1, 3}, {pair{0, 2}, pair{0, 2}}, true},
        // The mirror image: a *cover* value that falls inside the domain's hole
        // (3 is covered, the first variable does not have it). The subtraction
        // then has to step over an interval of the cover that matches nothing at
        // all, which is a different position in the merge from the row above.
        {{vector<int>{0, 1, 2, 4, 5, 6}, pair{0, 6}}, {0, 3, 6}, {pair{0, 2}, pair{0, 2}, pair{0, 2}}, true},
        // Cover values spanning zero, with a bit-aliased {0,1}-domain variable in
        // the Hall set (issue #557): the aliased variable's (== 0)/(== 1) atoms are
        // ~b0/b0, a complementary pair, which made the demand-aggregate at-most-one
        // loose and broke the proof. These faithful negative mirrors of the
        // positive cases above exercise the fixed recover_am1 block scheme. Closed
        // span-zero (the primary reproducer): fails ~half the branching seeds
        // before the fix.
        {{pair{-1, 1}, pair{-1, 1}, pair{0, 1}}, {-1, 0, 1}, {pair{0, 3}, pair{0, 3}, pair{0, 3}}, true},
        // Upper-capacity Hall, all-negative-plus-zero domains: three vars confined
        // to {-2,-1} with capacity 2+1 force the fourth off value -1.
        {{pair{-2, -1}, pair{-2, -1}, pair{-2, -1}, pair{-2, 0}}, {-2, -1}, {pair{0, 2}, pair{0, 1}}, false},
        // Lower-demand Hall over a span-zero cover: value -1 demanded twice with a
        // {0,1}-aliased supplier among the potential vars.
        {{pair{-2, 1}, pair{-2, 1}, pair{-1, 2}}, {-2, -1}, {pair{2, 3}, pair{0, 3}}, false},
        // Bounded form, value absent from a domain.
        {{pair{1, 3}, pair{1, 3}, pair{1, 3}}, {1, 2}, {pair{1, 3}, pair{0, 1}}, false},
        // Degenerate cases (issue #254): empty vars, empty value set, single
        // value, and all-constant vars/counts in both directions.
        {{}, {1}, {0}, false},                                // empty vars, open: count of 1 is 0 (tautology)
        {{}, {1}, {1}, false},                                // empty vars, open: count can't be 1 (contradiction)
        {{}, {1}, {0}, true},                                 // empty vars, closed: vacuously satisfied
        {{5}, {5}, {1}, false},                               // single all-const var matches value (tautology)
        {{5}, {3}, {1}, false},                               // count of absent value can't be 1 (contradiction)
        {{1, 1, 2}, {1, 2}, {2, 1}, false},                   // all-const vars + counts, correct (tautology)
        {{1, 1, 2}, {1, 2}, {1, 1}, false},                   // all-const vars + counts, wrong count (contradiction)
        {{pair{1, 2}, pair{1, 2}}, {1}, {pair{0, 2}}, false}, // single cover value
        {{pair{1, 2}}, {}, {}, false},                        // empty value set, open: any assignment allowed
    };

    mt19937 rand(*get_seed());
    for (int iteration = 0; iteration < 24; ++iteration) {
        uniform_int_distribution n_vars_dist(2, 3);
        uniform_int_distribution n_values_dist(1, 2);
        uniform_int_distribution lo_dist(0, 2);
        uniform_int_distribution width_dist(0, 2);
        uniform_int_distribution value_dist(0, 3);
        uniform_int_distribution count_hi_dist(0, 3);
        uniform_int_distribution closed_dist(0, 1);

        auto n_vars = n_vars_dist(rand);
        vector<Range> vars_range;
        for (int i = 0; i < n_vars; ++i) {
            auto lo = lo_dist(rand);
            vars_range.emplace_back(pair{lo, lo + width_dist(rand)});
        }

        auto n_values = n_values_dist(rand);
        set<int> value_set;
        while (static_cast<int>(value_set.size()) < n_values)
            value_set.insert(value_dist(rand));
        vector<int> values(value_set.begin(), value_set.end());

        vector<Range> counts_range;
        for (int i = 0; i < n_values; ++i) {
            auto hi = count_hi_dist(rand);
            counts_range.emplace_back(pair{0, hi});
        }

        data.emplace_back(vars_range, values, counts_range, closed_dist(rand) == 1);
    }

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & [vars_range, values, counts_range, closed] : data)
            run_bgcc_test(proofs, vars_range, values, counts_range, closed);
        for (auto & [under_ranges, positions, values, counts_range, closed] : aliased_views_data())
            run_aliased_views_test(proofs, under_ranges, positions, values, counts_range, closed);
        for (int n : {4, 5, 6, 7})
            for (bool closed : {false, true})
                run_magic_sequence_test(proofs, n, closed);
    }

    return EXIT_SUCCESS;
}
