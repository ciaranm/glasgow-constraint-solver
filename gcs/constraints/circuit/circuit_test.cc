#include <gcs/constraints/circuit.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstddef>
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

// A successor assignment is a single Hamiltonian circuit iff, following the
// successor pointers from node 0, we visit all n nodes exactly once and
// return to 0 on step n. This rejects both sub-circuits and non-permutations.
auto is_single_circuit(const vector<int> & succ) -> bool
{
    auto n = succ.size();
    vector<bool> visited(n, false);
    std::size_t cur = 0, count = 0;
    while (! visited[cur]) {
        visited[cur] = true;
        if (succ[cur] < 0 || std::cmp_greater_equal(succ[cur], n))
            return false;
        cur = static_cast<std::size_t>(succ[cur]);
        ++count;
    }
    return cur == 0 && count == n;
}

auto run_circuit_test(bool proofs, const ViewWrapConfig & view_cfg, int n) -> void
{
    auto wraps = wraps_for_positions(view_cfg, n);
    print(cerr, "circuit [{}] n={}{}", view_wrap_config_label(view_cfg), n, proofs ? " with proofs:" : ":");
    cerr << flush;

    vector<pair<int, int>> domains(static_cast<std::size_t>(n), pair{0, n - 1});

    set<tuple<vector<int>>> expected, actual;
    build_expected(expected, [&](vector<int> succ) { return is_single_circuit(succ); }, domains);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> succ;
    for (int i = 0; i < n; ++i)
        succ.push_back(create_integer_variable_or_constant_with_view(p, pair{0, n - 1}, wraps.at(static_cast<std::size_t>(i))));
    p.post(Circuit{succ});

    auto proof_name = proofs ? make_optional("circuit_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{succ});
    check_results(proof_name, expected, actual);
}

auto main(int argc, char * argv[]) -> int
{
    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    // Instances run at n = 3, 4, 5; positions 0..4 cover the largest fully.
    constexpr int n_positions = 5;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "circuit view sweep: position {} out of range for n_positions = {}; skipping",
            *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (int n : {3, 4, 5})
            run_circuit_test(proofs, view_cfg, n);
    }

    return EXIT_SUCCESS;
}
