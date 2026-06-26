#include <gcs/constraints/increasing.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
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

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
using fmt::println;
#endif

using namespace gcs;
using namespace gcs::test_innards;

enum class IncVariant
{
    Increasing,
    StrictlyIncreasing,
    Decreasing,
    StrictlyDecreasing
};

template <IncVariant V>
auto satisfied(const vector<int> & a) -> bool
{
    for (size_t i = 0; i + 1 < a.size(); ++i) {
        if constexpr (V == IncVariant::Increasing) {
            if (a[i] > a[i + 1])
                return false;
        }
        else if constexpr (V == IncVariant::StrictlyIncreasing) {
            if (a[i] >= a[i + 1])
                return false;
        }
        else if constexpr (V == IncVariant::Decreasing) {
            if (a[i] < a[i + 1])
                return false;
        }
        else {
            if (a[i] <= a[i + 1])
                return false;
        }
    }
    return true;
}

template <IncVariant V>
auto post_inc(Problem & p, vector<IntegerVariableID> vars) -> void
{
    if constexpr (V == IncVariant::Increasing)
        p.post(Increasing{std::move(vars)});
    else if constexpr (V == IncVariant::StrictlyIncreasing)
        p.post(StrictlyIncreasing{std::move(vars)});
    else if constexpr (V == IncVariant::Decreasing)
        p.post(Decreasing{std::move(vars)});
    else
        p.post(StrictlyDecreasing{std::move(vars)});
}

template <IncVariant V>
auto variant_name() -> const char *
{
    if constexpr (V == IncVariant::Increasing)
        return "increasing";
    else if constexpr (V == IncVariant::StrictlyIncreasing)
        return "strictly_increasing";
    else if constexpr (V == IncVariant::Decreasing)
        return "decreasing";
    else
        return "strictly_decreasing";
}

template <IncVariant V>
auto run_inc_test(bool proofs, const ViewWrapConfig & view_cfg, const vector<variant<int, pair<int, int>>> & domains) -> void
{
    auto wraps = wraps_for_positions(view_cfg, static_cast<int>(domains.size()));
    print(cerr, "{} [{}] {}{}", variant_name<V>(), view_wrap_config_label(view_cfg), domains, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<vector<int>>> expected, actual;
    build_expected(expected, [](vector<int> v) { return satisfied<V>(v); }, domains);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> vars;
    for (std::size_t i = 0; i < domains.size(); ++i)
        vars.push_back(visit([&](auto e) { return create_integer_variable_or_constant_with_view(p, e, wraps.at(i)); }, domains[i]));
    post_inc<V>(p, vars);

    auto proof_name = proofs ? make_optional("increasing_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{vars});
    check_results(proof_name, expected, actual);
}

template <IncVariant V>
auto run_all_for_variant(bool proofs, const ViewWrapConfig & view_cfg) -> void
{
    // Trivial cases.
    run_inc_test<V>(proofs, view_cfg, {});
    run_inc_test<V>(proofs, view_cfg, {pair{0, 3}});

    // Pairs.
    run_inc_test<V>(proofs, view_cfg, {pair{0, 3}, pair{0, 3}});
    run_inc_test<V>(proofs, view_cfg, {pair{2, 5}, pair{0, 3}});

    // Triples — exercise both forward and backward sweeps.
    run_inc_test<V>(proofs, view_cfg, {pair{0, 3}, pair{0, 3}, pair{0, 3}});
    run_inc_test<V>(proofs, view_cfg, {pair{1, 2}, pair{0, 5}, pair{3, 4}});

    // A negative-domain case.
    run_inc_test<V>(proofs, view_cfg, {pair{-2, 1}, pair{-1, 2}, pair{0, 3}});

    // Tight infeasible / nearly-infeasible for strict variants.
    run_inc_test<V>(proofs, view_cfg, {pair{0, 2}, pair{0, 2}, pair{0, 2}, pair{0, 2}});

    // Length 5 to exercise the propagator on a longer chain.
    run_inc_test<V>(proofs, view_cfg, {pair{0, 4}, pair{0, 4}, pair{0, 4}, pair{0, 4}, pair{0, 4}});

    // Constant entries pinning the chain at a fixed value.
    run_inc_test<V>(proofs, view_cfg, {pair{0, 5}, 3, pair{0, 5}});
    run_inc_test<V>(proofs, view_cfg, {2, pair{0, 5}, 4});

    // All-constant chains (issue #254): genuine ConstantIntegerVariableIDs,
    // so each variant reduces to a true/false check. build_expected computes
    // the per-variant truth, covering both directions: e.g. {1,2,3} satisfies
    // (Strictly)Increasing but not the Decreasing variants; {2,2,3} satisfies
    // Increasing but not StrictlyIncreasing; {3,2,1} the mirror image.
    run_inc_test<V>(proofs, view_cfg, {1, 2, 3});
    run_inc_test<V>(proofs, view_cfg, {2, 2, 3});
    run_inc_test<V>(proofs, view_cfg, {3, 2, 1});
    run_inc_test<V>(proofs, view_cfg, {2, 2, 2});
    // Mixed: a genuine constant plus a singleton-domain variable.
    run_inc_test<V>(proofs, view_cfg, {1, pair{2, 2}, 3});
}

// Dup-variable test: Increasing/Decreasing variants with the same
// handle in two adjacent positions. Non-strict variants are tautological
// at the dup point (x <= x / x >= x); strict variants are UNSAT
// (x < x / x > x). Consistency isn't checked on dup runs; see
// tmp/duplicate_var_audit.md.
template <IncVariant V>
auto run_dup_inc_test(bool proofs, const vector<pair<int, int>> & unique_domains, const vector<int> & positions) -> void
{
    print(cerr, "{} dup domains={} positions={}{}", variant_name<V>(), unique_domains, positions, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<vector<int>>> expected, actual;
    build_expected(
        expected,
        [&](const vector<int> & vals) -> bool {
            vector<int> v;
            for (auto pos : positions)
                v.push_back(vals.at(pos));
            return satisfied<V>(v);
        },
        unique_domains);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> unique_vars;
    for (const auto & d : unique_domains)
        unique_vars.push_back(p.create_integer_variable(Integer(d.first), Integer(d.second)));
    vector<IntegerVariableID> array;
    for (auto pos : positions)
        array.push_back(unique_vars.at(pos));
    post_inc<V>(p, array);

    auto proof_name = proofs ? make_optional("increasing_test_dup") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{unique_vars});
    check_results(proof_name, expected, actual);
}

auto main(int argc, char * argv[]) -> int
{
    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    constexpr int n_positions = 5;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "increasing view sweep: position {} out of range for n_positions = {}; skipping", *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    random_device rand_dev;
    mt19937 rand(rand_dev());

    auto random_run = [&]<IncVariant V>(bool proofs) {
        // Sizes 2..5 with modest domains. For Increasing and 5 vars over a
        // 6-value domain the worst case is C(6+5-1, 5) = 252 solutions; the
        // strict variants are smaller. VeriPB stays fast on these.
        uniform_int_distribution n_vars_dist{2, 5};
        int n_vars = n_vars_dist(rand);
        vector<variant<int, pair<int, int>>> doms;
        for (int i = 0; i < n_vars; ++i)
            doms.emplace_back(generate_random_data_item(rand, random_bounds_or_constant(-3, 3, 2, 4)));
        run_inc_test<V>(proofs, view_cfg, doms);
    };

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        run_all_for_variant<IncVariant::Increasing>(proofs, view_cfg);
        run_all_for_variant<IncVariant::StrictlyIncreasing>(proofs, view_cfg);
        run_all_for_variant<IncVariant::Decreasing>(proofs, view_cfg);
        run_all_for_variant<IncVariant::StrictlyDecreasing>(proofs, view_cfg);

        for (int x = 0; x < 5; ++x) {
            random_run.template operator()<IncVariant::Increasing>(proofs);
            random_run.template operator()<IncVariant::StrictlyIncreasing>(proofs);
            random_run.template operator()<IncVariant::Decreasing>(proofs);
            random_run.template operator()<IncVariant::StrictlyDecreasing>(proofs);
        }

        if (view_wrap_config_is_effectively_bare(view_cfg, n_positions)) {
            // {x, x} — non-strict tautology, strict UNSAT.
            run_dup_inc_test<IncVariant::Increasing>(proofs, {{1, 5}}, {0, 0});
            run_dup_inc_test<IncVariant::StrictlyIncreasing>(proofs, {{1, 5}}, {0, 0});
            run_dup_inc_test<IncVariant::Decreasing>(proofs, {{1, 5}}, {0, 0});
            run_dup_inc_test<IncVariant::StrictlyDecreasing>(proofs, {{1, 5}}, {0, 0});
            // {x, x, y} — non-strict: x <= y for any x; strict: UNSAT.
            run_dup_inc_test<IncVariant::Increasing>(proofs, {{1, 5}, {1, 5}}, {0, 0, 1});
            run_dup_inc_test<IncVariant::StrictlyIncreasing>(proofs, {{1, 5}, {1, 5}}, {0, 0, 1});
            // {x, y, x} — interesting: forces y == x in non-strict, UNSAT in strict.
            run_dup_inc_test<IncVariant::Increasing>(proofs, {{1, 4}, {1, 4}}, {0, 1, 0});
            run_dup_inc_test<IncVariant::StrictlyIncreasing>(proofs, {{1, 4}, {1, 4}}, {0, 1, 0});
        }
    }
    return EXIT_SUCCESS;
}
