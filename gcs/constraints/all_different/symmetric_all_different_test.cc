#include <gcs/constraints/all_different/symmetric_all_different.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <functional>
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
#include <fmt/ranges.h>
#endif

using std::cerr;
using std::flush;
using std::function;
using std::make_optional;
using std::nullopt;
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

namespace
{
    auto enumerate_assignments(set<tuple<vector<int>>> & expected,
        const vector<vector<int>> & domains,
        const function<auto(const vector<int> &)->bool> & is_satisfying) -> void
    {
        vector<int> current;
        function<auto(std::size_t)->void> recurse = [&](std::size_t pos) -> void {
            if (pos == domains.size()) {
                if (is_satisfying(current))
                    expected.emplace(current);
                return;
            }
            for (int v : domains[pos]) {
                current.push_back(v);
                recurse(pos + 1);
                current.pop_back();
            }
        };
        recurse(0);
    }

    auto run_symalldiff_test(bool proofs, bool expect_gac, const vector<vector<int>> & domains, int start) -> void
    {
        print(cerr, "symmetric_all_different {} start {} {}{}", domains, start,
            expect_gac ? "(GAC)" : "(consistent only)", proofs ? " with proofs:" : ":");
        cerr << flush;

        const int n = static_cast<int>(domains.size());

        auto is_satisfying = [&](const vector<int> & v) -> bool {
            for (int i = 0; i < n; ++i)
                for (int j = i + 1; j < n; ++j)
                    if (v[i] == v[j])
                        return false;
            for (int x : v)
                if (x < start || x >= start + n)
                    return false;
            for (int i = 0; i < n; ++i)
                if (v[v[i] - start] != i + start)
                    return false;
            return true;
        };

        set<tuple<vector<int>>> expected, actual;
        enumerate_assignments(expected, domains, is_satisfying);
        println(cerr, " expecting {} solutions", expected.size());

        Problem p;
        vector<IntegerVariableID> vars;
        for (const auto & d : domains) {
            vector<Integer> vals;
            for (int v : d)
                vals.push_back(Integer(v));
            vars.push_back(p.create_integer_variable(vals));
        }
        p.post(SymmetricAllDifferent{vars, Integer(start)});

        auto proof_name = proofs ? make_optional("symmetric_all_different_test") : nullopt;
        if (expect_gac)
            solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{vars});
        else
            solve_for_tests(p, proof_name, actual, tuple{vars});
        check_results(proof_name, expected, actual);
    }

    auto run_all_tests(bool proofs) -> void
    {
        // Trivial sizes.
        run_symalldiff_test(proofs, true, {}, 0);
        run_symalldiff_test(proofs, true, {{0}}, 0);
        run_symalldiff_test(proofs, true, {{1}}, 1);

        // Small unrestricted: AllDifferent-GAC + Inverse-channeling reaches
        // full symmetric-alldiff GAC for these.
        run_symalldiff_test(proofs, true, {{0, 1}, {0, 1}}, 0);
        run_symalldiff_test(proofs, true, {{1, 2}, {1, 2}}, 1);
        run_symalldiff_test(proofs, true, {{0, 1, 2}, {0, 1, 2}, {0, 1, 2}}, 0);
        run_symalldiff_test(proofs, true, {{0, 1, 2, 3}, {0, 1, 2, 3}, {0, 1, 2, 3}, {0, 1, 2, 3}}, 0);

        // Out-of-range value gets bound-trimmed by Inverse before propagation.
        run_symalldiff_test(proofs, true, {{0, 1, 5}, {0, 1}}, 0);

        // Cases where AllDifferent-GAC + Inverse-channeling is strictly
        // weaker than the symmetric-alldifferent GAC of Régin (1999).
        // GAC for the latter requires non-bipartite matching on the
        // symmetry graph G (edge (i,j) iff j in D(x_i) and i in D(x_j));
        // we only get pairwise channeling and a bipartite matching, which
        // miss global structural infeasibilities. solve_for_tests rather
        // than solve_for_tests_checking_gac for these.

        // Unique solution [1,0,3,2]. The bipartite matching x_0=2,
        // x_1=0, x_2=1, x_3=3 supports x_0=2 for AllDifferent, but it
        // is a 3-cycle (x_0 -> 2 -> x_2 -> 1 -> x_1 -> 0 -> x_0) plus a
        // fixed point, not an involution; the Inverse propagator only
        // checks pair-edges of G, so x_0=2 is not pruned at the root.
        run_symalldiff_test(proofs, false,
            {{1, 2}, {0, 2}, {0, 1, 3}, {2, 3}}, 0);

        // Triangle: G = K_3, which has no perfect matching, so the
        // expected set is empty. AllDifferent-GAC accepts the bipartite
        // matching x_0=1, x_1=2, x_2=0 (a 3-cycle), and channeling on
        // each pair sees the symmetric edge in place. Neither catches
        // the absent perfect matching.
        run_symalldiff_test(proofs, false, {{1, 2}, {0, 2}, {0, 1}}, 0);

        // Same triangle plus a forced fixed point on the side.
        run_symalldiff_test(proofs, false, {{1, 2}, {0, 2}, {0, 1}, {3}}, 0);
    }
}

auto main(int, char *[]) -> int
{
    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        run_all_tests(proofs);
    }
    return EXIT_SUCCESS;
}
