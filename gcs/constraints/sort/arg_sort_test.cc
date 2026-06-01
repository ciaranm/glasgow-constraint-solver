#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/sort.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
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
        solve_for_tests(prob, proof_name, actual, tuple{x, p});
        check_results(proof_name, expected, actual);
    }
}

auto main(int, char *[]) -> int
{
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
    }

    return EXIT_SUCCESS;
}
