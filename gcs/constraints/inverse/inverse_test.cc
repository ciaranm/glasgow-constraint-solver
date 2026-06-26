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

auto run_inverse_test(bool proofs, const ViewWrapConfig & view_cfg, const vector<variant<int, pair<int, int>>> & x_range,
    const vector<variant<int, pair<int, int>>> & y_range) -> void
{
    auto wraps = wraps_for_positions(view_cfg, static_cast<int>(x_range.size() + y_range.size()));
    print(cerr, "inverse [{}] {} {} {}", view_wrap_config_label(view_cfg), x_range, y_range, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<vector<int>, vector<int>>> expected, actual;
    build_expected(
        expected,
        [&](const vector<int> & x, const vector<int> & y) {
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
    std::size_t pos = 0;
    for (const auto & entry : x_range) {
        auto w = wraps.at(pos++);
        x.push_back(visit([&](auto e) { return create_integer_variable_or_constant_with_view(p, e, w); }, entry));
    }
    for (const auto & entry : y_range) {
        auto w = wraps.at(pos++);
        y.push_back(visit([&](auto e) { return create_integer_variable_or_constant_with_view(p, e, w); }, entry));
    }
    p.post(Inverse{x, y});

    auto proof_name = proofs ? make_optional("inverse_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{x, y});

    check_results(proof_name, expected, actual);
}

auto main(int argc, char * argv[]) -> int
{
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
        {{}, {}},
        // Boundary: singleton — forces both to 0.
        {{pair{0, 0}}, {pair{0, 0}}}, {{pair{0, 5}}, {pair{0, 5}}},
        // Existing hand-rolled cases.
        {{pair{0, 2}, pair{0, 2}, pair{0, 2}}, {pair{0, 2}, pair{0, 2}, pair{0, 2}}},
        {{pair{0, 2}, pair{1, 3}, pair{0, 2}, pair{0, 3}}, {pair{0, 3}, pair{1, 2}, pair{1, 3}, pair{0, 3}}},
        {{pair{0, 2}, pair{0, 2}, pair{0, 2}, pair{0, 4}, pair{0, 4}}, {pair{0, 4}, pair{0, 4}, pair{0, 4}, pair{3, 4}, pair{3, 4}}},
        // Constant entries pin one inverse pair.
        {{1, pair{0, 2}, pair{0, 2}}, {pair{0, 2}, 0, pair{0, 2}}},
        {{pair{0, 3}, pair{0, 3}, 0, pair{0, 3}}, {2, pair{0, 3}, pair{0, 3}, pair{0, 3}}},
        // Issue #171 regression: two array positions pinned to the same constant
        // makes the constraint infeasible (Inverse forces a permutation). The
        // recovered "AM1" line for the duplicate-pinned value is now a direct
        // `0 ≥ 1` contradiction, which downstream pol expressions sum into a
        // valid contradiction proof.
        {{3, 2, 3, pair{0, 3}}, {pair{0, 3}, pair{0, 3}, pair{0, 3}, pair{0, 3}}},
        {{pair{0, 3}, pair{0, 3}, pair{0, 3}, pair{0, 3}}, {1, pair{0, 3}, 1, pair{0, 3}}},
        // issue #254: fully all-constant arguments, both directions.
        {{0, 1}, {0, 1}},  // identity permutation, consistent (tautology)
        {{1, 0}, {1, 0}},  // swap: x[0]=1<->y[1]=0, x[1]=0<->y[0]=1, consistent (tautology)
        {{1, 0}, {0, 1}}}; // x swapped but y identity: inconsistent (contradiction)

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
            run_inverse_test(proofs, view_cfg, x, y);
    }

    {
        // Intra-array duplicates make Inverse trivially infeasible: reject
        // at construction. Cross-array aliasing (e.g. Inverse(x, x) for
        // involutions) is legitimate and stays accepted.
        auto expect_throw = [](auto build) {
            try {
                build();
            }
            catch (const InvalidProblemDefinitionException &) {
                return true;
            }
            return false;
        };

        Problem p;
        auto x = p.create_integer_variable_vector(3, 0_i, 2_i);
        auto y = p.create_integer_variable_vector(3, 0_i, 2_i);

        if (! expect_throw([&] { p.post(Inverse{{x[0], x[1], x[0]}, y}); })) {
            cerr << "expected Inverse with duplicate in first array to throw\n";
            return EXIT_FAILURE;
        }
        if (! expect_throw([&] { p.post(Inverse{x, {y[0], y[2], y[2]}}); })) {
            cerr << "expected Inverse with duplicate in second array to throw\n";
            return EXIT_FAILURE;
        }
    }

    return EXIT_SUCCESS;
}
