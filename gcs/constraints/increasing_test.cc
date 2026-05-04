#include <gcs/constraints/increasing.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

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
            if (a[i] > a[i + 1]) return false;
        }
        else if constexpr (V == IncVariant::StrictlyIncreasing) {
            if (a[i] >= a[i + 1]) return false;
        }
        else if constexpr (V == IncVariant::Decreasing) {
            if (a[i] < a[i + 1]) return false;
        }
        else {
            if (a[i] <= a[i + 1]) return false;
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
    if constexpr (V == IncVariant::Increasing) return "increasing";
    else if constexpr (V == IncVariant::StrictlyIncreasing) return "strictly_increasing";
    else if constexpr (V == IncVariant::Decreasing) return "decreasing";
    else return "strictly_decreasing";
}

template <IncVariant V>
auto run_inc_test(bool proofs, const vector<pair<int, int>> & domains) -> void
{
    print(cerr, "{} {}{}", variant_name<V>(), domains, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<vector<int>>> expected, actual;
    build_expected(expected, [](vector<int> v) { return satisfied<V>(v); }, domains);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> vars;
    for (const auto & d : domains)
        vars.push_back(p.create_integer_variable(Integer(d.first), Integer(d.second)));
    post_inc<V>(p, vars);

    auto proof_name = proofs ? make_optional("increasing_test") : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{vars});
    check_results(proof_name, expected, actual);
}

template <IncVariant V>
auto run_all_for_variant(bool proofs) -> void
{
    // Trivial cases.
    run_inc_test<V>(proofs, {});
    run_inc_test<V>(proofs, {{0, 3}});

    // Pairs.
    run_inc_test<V>(proofs, {{0, 3}, {0, 3}});
    run_inc_test<V>(proofs, {{2, 5}, {0, 3}});

    // Triples — exercise both forward and backward sweeps.
    run_inc_test<V>(proofs, {{0, 3}, {0, 3}, {0, 3}});
    run_inc_test<V>(proofs, {{1, 2}, {0, 5}, {3, 4}});

    // A negative-domain case.
    run_inc_test<V>(proofs, {{-2, 1}, {-1, 2}, {0, 3}});

    // Tight infeasible / nearly-infeasible for strict variants.
    run_inc_test<V>(proofs, {{0, 2}, {0, 2}, {0, 2}, {0, 2}});

    // Length 5 to exercise the propagator on a longer chain.
    run_inc_test<V>(proofs, {{0, 4}, {0, 4}, {0, 4}, {0, 4}, {0, 4}});
}

auto main(int, char *[]) -> int
{
    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        run_all_for_variant<IncVariant::Increasing>(proofs);
        run_all_for_variant<IncVariant::StrictlyIncreasing>(proofs);
        run_all_for_variant<IncVariant::Decreasing>(proofs);
        run_all_for_variant<IncVariant::StrictlyDecreasing>(proofs);
    }
    return EXIT_SUCCESS;
}
