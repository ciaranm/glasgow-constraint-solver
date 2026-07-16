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
        build_expected(expected, [&](const vector<int> & x, const vector<int> & p) { return is_arg_sort(x, p, offset); }, x_domains, p_domains);
        println(cerr, " expecting {} solutions", expected.size());

        Problem prob;
        vector<IntegerVariableID> x, p;
        for (const auto & d : x_domains)
            x.push_back(prob.create_integer_variable(Integer(d.first), Integer(d.second)));
        for (const auto & d : p_domains)
            p.push_back(prob.create_integer_variable(Integer(d.first), Integer(d.second)));
        prob.post(ArgSort{x, p, Integer(offset)});

        auto proof_name = proofs ? make_optional("arg_sort_test") : nullopt;
        // Neither x nor p is bounds(Z)-consistent for the *stable* ArgSort, so we
        // only check full enumeration + the proof here (not per-node consistency).
        // The reused Mehlhorn-Thiel propagator is bounds(Z) on x and the internal
        // sorted values, but only for the bare Sortedness(x; y) relation, where
        // the permutation is unconstrained. The stable tie-break that pins a
        // unique p makes both sides strictly tighter than MT delivers:
        //  - x gains strict bounds (p[j] > p[j+1] forces x[p[j]] < x[p[j+1]], so a
        //    value that could only tie at an extremum is dead);
        //  - p gains joint infeasibilities -- the achievable-rank-set propagator
        //    derives each element's ranks from the x intervals but not from the
        //    *other* p domains, so e.g. fixing one p position can kill another rank
        //    that the per-element reachable set still admits.
        // Thiel's thesis sec 3.1.4 shows even the non-stable SortednessPerm is not
        // bounds(Z) on x or p (Lemma 3.1 breaks down), with a counterexample; the
        // stable variant is tighter again and no bounds(Z) algorithm for it is
        // known. So check None on both (#413).
        solve_for_tests(prob, proof_name, actual, tuple{x, p});
        check_results(proof_name, expected, actual);
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

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

        // Degenerate (issue #254): empty input (vacuously satisfied) and
        // all-fixed inputs (the permutation is uniquely determined), 0- and
        // 1-based.
        run_arg_sort_test(proofs, 0, {});                       // empty input
        run_arg_sort_test(proofs, 0, {{5, 5}});                 // single fixed: p[0]==offset
        run_arg_sort_test(proofs, 0, {{3, 3}, {1, 1}, {2, 2}}); // all fixed distinct, 0-based
        run_arg_sort_test(proofs, 1, {{3, 3}, {1, 1}, {2, 2}}); // all fixed distinct, 1-based

        // Negative values.
        run_arg_sort_test(proofs, 0, {{-2, 0}, {-2, 0}});

        // Separated domains: the element order is fixed (x[1] < x[2] < x[0])
        // before any x value is, so the channel propagator must prune p via the
        // disjoint-domain rule (p[0]=1, p[1]=2, p[2]=0) -- exercises rule (1)'s
        // RUP justification.
        run_arg_sort_test(proofs, 0, {{4, 5}, {0, 1}, {2, 3}});
        run_arg_sort_test(proofs, 1, {{4, 5}, {0, 1}, {2, 3}});

        // Tie-induced rank HOLES: with x[0] = x[1] = 0 the "number below x[2]"
        // jumps from 0 to 2 as x[2] crosses 0, so x[2]'s reachable ranks are
        // {0, 2} (never 1). The achievable-rank-set propagator must prune p[1]=2,
        // exercising the threshold-pivot hole proof (not the plain interval pol).
        run_arg_sort_test(proofs, 0, {{0, 0}, {0, 0}, {-1, 1}});
        run_arg_sort_test(proofs, 1, {{0, 0}, {0, 0}, {-1, 1}});
        // A wider hole: x[2] in [-2,0] reaches ranks {0, 3} only (holes at 1, 2).
        run_arg_sort_test(proofs, 0, {{0, 0}, {0, 0}, {-2, 0}, {-1, -1}, {3, 5}});
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
        mt19937 rng(*get_seed());
        for (int t = 0; t < 8; ++t) {
            auto xd = random_x_domains(rng);
            run_arg_sort_test(proofs, t % 2, xd);
        }
    }

    return EXIT_SUCCESS;
}
