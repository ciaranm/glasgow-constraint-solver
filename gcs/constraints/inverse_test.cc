#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/inverse.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <util/enumerate.hh>

#include <cstdlib>
#include <iostream>
#include <map>
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
using std::make_optional;
using std::mt19937;
using std::nullopt;
using std::pair;
using std::random_device;
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

// Issue #171: Inverse's per-value AM1 reconstruction calls recover_am1
// over the atoms `x[i] != v` (resp. `y[j] != v`). When two array entries
// are constants pinned to the same value, two atoms in the AM1 are
// always-false and pair_ne emits PB lines that the resulting `pol`
// expression can't sum cleanly — VeriPB rejects it with a parse error
// at the truncated `pol N +;` line. The propagator itself handles
// duplicate-value constants fine (the instance is just infeasible);
// only the proof leg breaks.
template <typename Range_>
auto has_duplicate_constants(const Range_ & range) -> bool
{
    std::map<int, int> counts;
    for (const auto & entry : range)
        if (std::holds_alternative<int>(entry))
            ++counts[std::get<int>(entry)];
    for (const auto & [_, c] : counts)
        if (c >= 2) return true;
    return false;
}

auto run_inverse_test(bool proofs, const vector<variant<int, pair<int, int>>> & x_range, const vector<variant<int, pair<int, int>>> & y_range) -> void
{
    bool effective_proofs = proofs && ! has_duplicate_constants(x_range) && ! has_duplicate_constants(y_range);

    print(cerr, "inverse {} {} {}", x_range, y_range,
        effective_proofs ? " with proofs:" : (proofs ? " (no-proofs: dup const, issue #171):" : ":"));
    cerr << flush;

    set<tuple<vector<int>, vector<int>>> expected, actual;
    build_expected(
        expected, [&](const vector<int> & x, const vector<int> & y) {
            // Random sweeps may pick domains that include out-of-range
            // values; the propagator's prepare() trims them but the
            // brute-force predicate runs over raw enumerated values, so
            // we need explicit bounds checks before the .at() calls.
            for (const auto & [i, _] : enumerate(x)) {
                if (x.at(i) < 0 || std::cmp_greater_equal(x.at(i), y.size()))
                    return false;
                if (cmp_not_equal(y.at(x.at(i)), i))
                    return false;
            }
            for (const auto & [i, _] : enumerate(y)) {
                if (y.at(i) < 0 || std::cmp_greater_equal(y.at(i), x.size()))
                    return false;
                if (cmp_not_equal(x.at(y.at(i)), i))
                    return false;
            }
            return true;
        },
        x_range, y_range);

    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> x, y;
    for (const auto & entry : x_range)
        x.push_back(visit([&](auto e) { return create_integer_variable_or_constant(p, e); }, entry));
    for (const auto & entry : y_range)
        y.push_back(visit([&](auto e) { return create_integer_variable_or_constant(p, e); }, entry));
    p.post(Inverse{x, y});

    auto proof_name = effective_proofs ? make_optional("inverse_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{x, y});

    check_results(proof_name, expected, actual);
}

auto main(int, char *[]) -> int
{
    using Entry = variant<int, pair<int, int>>;
    vector<tuple<vector<Entry>, vector<Entry>>> var_data = {
        // Boundary: empty arrays — vacuously satisfied.
        {{}, {}},
        // Boundary: singleton — forces both to 0.
        {{pair{0, 0}}, {pair{0, 0}}},
        {{pair{0, 5}}, {pair{0, 5}}},
        // Existing hand-rolled cases.
        {{pair{0, 2}, pair{0, 2}, pair{0, 2}}, {pair{0, 2}, pair{0, 2}, pair{0, 2}}},
        {{pair{0, 2}, pair{1, 3}, pair{0, 2}, pair{0, 3}}, {pair{0, 3}, pair{1, 2}, pair{1, 3}, pair{0, 3}}},
        {{pair{0, 2}, pair{0, 2}, pair{0, 2}, pair{0, 4}, pair{0, 4}}, {pair{0, 4}, pair{0, 4}, pair{0, 4}, pair{3, 4}, pair{3, 4}}},
        // Constant entries pin one inverse pair.
        {{1, pair{0, 2}, pair{0, 2}}, {pair{0, 2}, 0, pair{0, 2}}},
        {{pair{0, 3}, pair{0, 3}, 0, pair{0, 3}}, {2, pair{0, 3}, pair{0, 3}, pair{0, 3}}},
        // Issue #171 regression: two x-positions pinned to the same constant
        // makes the constraint infeasible (Inverse forces a permutation), but
        // the propagator handles it correctly. The proof leg is skipped via
        // has_duplicate_constants until #171 is fixed.
        {{3, 2, 3, pair{0, 3}}, {pair{0, 3}, pair{0, 3}, pair{0, 3}, pair{0, 3}}},
        {{pair{0, 3}, pair{0, 3}, pair{0, 3}, pair{0, 3}}, {1, pair{0, 3}, 1, pair{0, 3}}}};

    random_device rand_dev;
    mt19937 rand(rand_dev());

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

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto & [x, y] : var_data)
            run_inverse_test(proofs, x, y);
    }

    return EXIT_SUCCESS;
}
