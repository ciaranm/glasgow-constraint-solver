#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/sort.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <random>
#include <set>
#include <tuple>
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

namespace
{
    // p (values are indices, offset-based) is the stable sorting permutation of x.
    auto is_arg_sort(const vector<int> & x, const vector<int> & p, int offset) -> bool
    {
        auto n = x.size();
        // Permutation of {offset, ..., offset + n - 1}.
        vector<bool> seen(n, false);
        for (auto pv : p) {
            auto idx = pv - offset;
            if (idx < 0 || idx >= static_cast<int>(n) || seen[idx])
                return false;
            seen[idx] = true;
        }
        // Sorted with stable tie-break.
        for (size_t j = 0; j + 1 < n; ++j) {
            int a = x[p[j] - offset], b = x[p[j + 1] - offset];
            if (a > b || (a == b && p[j] >= p[j + 1]))
                return false;
        }
        return true;
    }

    auto run_arg_sort_test(bool proofs, int offset, const vector<pair<int, int>> & x_domains) -> void
    {
        auto n = x_domains.size();
        vector<pair<int, int>> p_domains(n, {offset, offset + static_cast<int>(n) - 1});

        print(cerr, "arg_sort offset={} x={}{}", offset, x_domains, proofs ? " with proofs:" : ":");
        cerr << flush;

        set<tuple<vector<int>, vector<int>>> expected, actual;
        build_expected(
            expected, [&](const vector<int> & x, const vector<int> & p) { return is_arg_sort(x, p, offset); },
            x_domains, p_domains);
        println(cerr, " expecting {} solutions", expected.size());

        Problem prob;
        vector<IntegerVariableID> x, p;
        for (const auto & d : x_domains)
            x.push_back(prob.create_integer_variable(Integer(d.first), Integer(d.second)));
        for (const auto & d : p_domains)
            p.push_back(prob.create_integer_variable(Integer(d.first), Integer(d.second)));
        prob.post(ArgSort{x, p, Integer(offset)});

        auto proof_name = proofs ? make_optional("arg_sort_test") : nullopt;
        // x is kept bounds(Z)-consistent by the reused Mehlhorn-Thiel propagator.
        // p is only channel-consistent (full bounds(Z) on p is the costly pass we
        // deliberately do not run), so it is not checked for a consistency level.
        solve_for_tests_checking_consistency(prob, proof_name, expected, actual,
            tuple{std::make_pair(x, CheckConsistency::BC), std::make_pair(p, CheckConsistency::None)});
        check_results(proof_name, expected, actual);
    }
}

auto main(int argc, char * argv[]) -> int
{
    set_seed_from_argv(argc, argv);

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;

        // Distinct values: the permutation is forced uniquely once x is fixed.
        run_arg_sort_test(proofs, 0, {{0, 3}, {0, 3}});
        run_arg_sort_test(proofs, 0, {{0, 2}, {0, 2}, {0, 2}});

        // Lots of ties -> exercises the stable tie-break heavily (e.g. all equal
        // forces p == identity).
        run_arg_sort_test(proofs, 0, {{0, 1}, {0, 1}, {0, 1}});

        // 1-based (MiniZinc convention).
        run_arg_sort_test(proofs, 1, {{0, 2}, {0, 2}, {0, 2}});

        // Single element: p[0] pinned to offset.
        run_arg_sort_test(proofs, 0, {{0, 5}});

        // Negative values.
        run_arg_sort_test(proofs, 0, {{-2, 0}, {-2, 0}});

        // Separated domains: the element order is fixed (x[1] < x[2] < x[0])
        // before any x value is, so the channel propagator must prune p via the
        // disjoint-domain rule (p[0]=1, p[1]=2, p[2]=0) -- exercises rule (1)'s
        // RUP justification.
        run_arg_sort_test(proofs, 0, {{4, 5}, {0, 1}, {2, 3}});
        run_arg_sort_test(proofs, 1, {{4, 5}, {0, 1}, {2, 3}});
    }

    // Seeded randomized batch: small instances with a mix of overlapping and
    // separated x domains, so the channel pruning and the GAC all_different on p
    // both get exercised. Reproduce a failure with --seed=N (the printed domains
    // also pin the instance down).
    auto random_x_domains = [](mt19937 & r) -> vector<pair<int, int>> {
        uniform_int_distribution<int> n_dist{2, 4}, lo_dist{-2, 3}, w_dist{0, 3};
        int n = n_dist(r);
        vector<pair<int, int>> xd;
        for (int i = 0; i < n; ++i) {
            int l = lo_dist(r);
            xd.emplace_back(l, l + w_dist(r));
        }
        return xd;
    };

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        auto seed = get_seed();
        mt19937 rng(seed ? *seed : random_device{}());
        for (int t = 0; t < 8; ++t) {
            auto xd = random_x_domains(rng);
            run_arg_sort_test(proofs, t % 2, xd);
        }
    }

    return EXIT_SUCCESS;
}
