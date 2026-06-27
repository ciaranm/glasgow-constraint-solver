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
using std::random_device;
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

using Range = variant<int, pair<int, int>>;

auto run_gacgcc_test(bool proofs, const vector<Range> & vars_range, const vector<int> & values, const vector<Range> & counts_range, bool closed)
    -> void
{
    print(cerr, "gacgcc vars={} values={} counts={} closed={}{}", vars_range, values, counts_range, closed, proofs ? " with proofs:" : ":");
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

    p.post(GACGlobalCardinality{vars, int_values, counts, closed});

    // Régin's flow makes the assignment variables GAC *relative to the count
    // bounds*: the network's value capacities are state.bounds(counts[j]), so it
    // never sees an interior hole in a count domain. Full GAC that respects count
    // holes is NP-hard (it couples to subset-sum over the counts). Once branching
    // punches a hole into a count domain, an assignment value can become globally
    // unsupported solely because some count is forced onto that hole -- invisible
    // to the bound-based flow (#413). So check the assignment variables at BC,
    // which treats the counts as intervals and matches what the flow guarantees;
    // the counts themselves are not checked.
    auto proof_name = proofs ? make_optional("gac_global_cardinality_test") : nullopt;
    solve_for_tests_checking_consistency(
        p, proof_name, expected, actual, tuple{pair{vars, CheckConsistency::BC}, pair{counts, CheckConsistency::None}});
    check_results(proof_name, expected, actual);
}

auto main(int, char *[]) -> int
{
    vector<tuple<vector<Range>, vector<int>, vector<Range>, bool>> data = {
        // Upper-capacity: first three confined to {1,2}, value 2 capped at 1,
        // so value 1 must take two of them; the fourth is forced off 1 and 2.
        {{pair{1, 2}, pair{1, 2}, pair{1, 2}, pair{1, 3}}, {1, 2}, {pair{0, 2}, pair{0, 1}}, false},
        // Lower-demand: value 1 needed at least twice, only two vars can supply.
        {{pair{1, 4}, pair{1, 4}, pair{2, 5}}, {1, 2}, {pair{2, 3}, pair{0, 3}}, false},
        // Infeasible by capacity.
        {{pair{1, 2}, pair{1, 2}, pair{1, 2}}, {1, 2}, {pair{0, 1}, pair{0, 1}}, false},
        // Open, exact counts.
        {{pair{1, 2}, pair{1, 2}}, {1, 2}, {pair{0, 2}, pair{0, 2}}, false},
        // Closed.
        {{pair{1, 3}, pair{1, 3}, pair{2, 3}}, {1, 2, 3}, {pair{0, 3}, pair{0, 3}, pair{0, 3}}, true},
        // A GAC-only pruning: AllDifferent-style Hall set (each value once).
        {{pair{1, 2}, pair{1, 2}, pair{1, 3}}, {1, 2, 3}, {pair{0, 1}, pair{0, 1}, pair{0, 1}}, false},
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

    random_device rand_dev;
    mt19937 rand(rand_dev());
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
            run_gacgcc_test(proofs, vars_range, values, counts_range, closed);
    }

    return EXIT_SUCCESS;
}
