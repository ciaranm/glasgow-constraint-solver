#include <gcs/constraints/circuit.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstddef>
#include <cstdlib>
#include <iostream>
#include <set>
#include <string>
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

enum struct CircuitPropagator
{
    scc,
    prevent
};

auto run_circuit_test(bool proofs, const ViewWrapConfig & view_cfg, int n, CircuitPropagator propagator) -> void
{
    auto wraps = wraps_for_positions(view_cfg, n);
    auto prop_label = propagator == CircuitPropagator::prevent ? "prevent" : "scc";
    print(cerr, "circuit/{} [{}] n={}{}", prop_label, view_wrap_config_label(view_cfg), n, proofs ? " with proofs:" : ":");
    cerr << flush;

    vector<pair<int, int>> domains(static_cast<std::size_t>(n), pair{0, n - 1});

    set<tuple<vector<int>>> expected, actual;
    build_expected(expected, [&](vector<int> succ) { return is_single_circuit(succ); }, domains);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> succ;
    for (int i = 0; i < n; ++i)
        succ.push_back(create_integer_variable_or_constant_with_view(p, pair{0, n - 1}, wraps.at(static_cast<std::size_t>(i))));
    if (propagator == CircuitPropagator::prevent)
        p.post(Circuit{succ}.with_algorithm(circuit::Prevent{}));
    else
        p.post(Circuit{succ}.with_algorithm(circuit::SCC{}));

    auto proof_name = proofs ? make_optional("circuit_test_" + std::string{prop_label} + "_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{succ});
    check_results(proof_name, expected, actual);
}

// A caller can hand over successors whose declared domains reach outside 0..n-1 --- a
// variable sized from a loop bound, or one shared with another constraint that needed a
// wider range. prepare() narrows them with define_bound() rather than rejecting them, and
// that guard is what the position encoding's range assumption rests on: `p[i]` rows exist
// for values 0..n-1 and nothing else keeps succ[i] inside that. Every other test here
// declares exactly 0..n-1, so without this one the guard is a no-op, and a no-op passes
// every check.
//
// Run bare rather than through the view sweep: a view's own bounds are what would be
// widened, and the guard is about the successor the constraint sees.
auto run_circuit_wide_domain_test(bool proofs, int n, CircuitPropagator propagator) -> void
{
    auto prop_label = propagator == CircuitPropagator::prevent ? "prevent" : "scc";
    print(cerr, "circuit/{} wide domains n={}{}", prop_label, n, proofs ? " with proofs:" : ":");
    cerr << flush;

    // Two either side, so a negative value, a value equal to n, and one beyond it are all
    // declared. is_single_circuit rejects every one of them, so the expected set is the
    // same as the 0..n-1 run's --- which is the point: the answer must not change.
    vector<pair<int, int>> domains(static_cast<std::size_t>(n), pair{-2, n + 1});

    set<tuple<vector<int>>> expected, actual;
    build_expected(expected, [&](vector<int> succ) { return is_single_circuit(succ); }, domains);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> succ;
    for (int i = 0; i < n; ++i)
        succ.push_back(p.create_integer_variable(-2_i, Integer{n + 1}));
    if (propagator == CircuitPropagator::prevent)
        p.post(Circuit{succ}.with_algorithm(circuit::Prevent{}));
    else
        p.post(Circuit{succ}.with_algorithm(circuit::SCC{}));

    auto proof_name = proofs ? make_optional("circuit_test_wide_" + std::string{prop_label}) : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{succ});
    check_results(proof_name, expected, actual);
}

// The empty successor array (issue #1307). MiniZinc's own decomposition special-cases it
// to `true`, so the free witness's two values are the solutions; until #1307 the SCC
// propagator crashed on it, and with proofs both algorithms threw on the position
// encoding's 0..-1 range.
auto run_empty_test(bool proofs, CircuitPropagator propagator) -> void
{
    auto prop_label = propagator == CircuitPropagator::scc ? "scc" : "prevent";
    println(cerr, "circuit/empty/{}{}", prop_label, proofs ? " with proofs:" : ":");

    Problem p;
    auto witness = p.create_integer_variable(0_i, 1_i);
    if (propagator == CircuitPropagator::scc)
        p.post(Circuit{vector<IntegerVariableID>{}}.with_algorithm(circuit::SCC{}));
    else
        p.post(Circuit{vector<IntegerVariableID>{}}.with_algorithm(circuit::Prevent{}));

    auto proof_name = proofs ? make_optional("circuit_test_empty_" + std::string{prop_label}) : nullopt;
    set<tuple<vector<int>>> expected{tuple{vector<int>{0}}, tuple{vector<int>{1}}}, actual;
    solve_for_tests(p, proof_name, actual, tuple{vector<IntegerVariableID>{witness}});
    check_results(proof_name, expected, actual);
}

// A long ring at the root, proofs off (issue #1327). The SCC walk used to recurse once per
// level of its depth-first tree, and on an 8 MiB stack it segfaulted from about 7,700 nodes;
// 20,000 is well past that. Two shapes: every successor fixed (one solution), and each node
// able to step one or two places on (stopped at the first node, after root propagation),
// since a shortcut for fixed input alone would leave the second exposed.
auto run_long_ring_test(bool fixed) -> bool
{
    constexpr int n = 20'000;
    println(cerr, "circuit/scc long ring n={} {}:", n, fixed ? "fixed" : "one or two on");

    Problem p;
    vector<IntegerVariableID> succ;
    for (int i = 0; i < n; ++i) {
        if (fixed)
            succ.push_back(constant_variable(Integer{(i + 1) % n}));
        else
            succ.push_back(p.create_integer_variable(vector<Integer>{Integer{(i + 1) % n}, Integer{(i + 2) % n}}));
    }
    p.post(Circuit{succ}.with_algorithm(circuit::SCC{}));

    long long solutions = 0;
    auto stats = solve_with(p,
        SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                           ++solutions;
                           return true;
                       },
            .trace = [&](const CurrentState &) -> bool { return fixed; },
            .stats_report = silent_stats_report()});
    auto want_solutions = fixed ? 1 : 0;
    if (solutions != want_solutions || stats.recursions != 1) {
        println(cerr, "  expected {} solutions in one recursion, got {} in {}", want_solutions, solutions, stats.recursions);
        return false;
    }
    return true;
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    // Instances run at n = 3, 4, 5; positions 0..4 cover the largest fully.
    constexpr int n_positions = 5;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "circuit view sweep: position {} out of range for n_positions = {}; skipping", *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto propagator : {CircuitPropagator::scc, CircuitPropagator::prevent}) {
            for (int n : {3, 4, 5})
                run_circuit_test(proofs, view_cfg, n, propagator);
            // Degenerate minimal circuits (issue #254): n=1 is a single self-loop
            // (the canonical minimal circuit), n=2 the unique 2-cycle. Run only in
            // the bare configuration; the view sweep targets the larger instances
            // and its positions can exceed these tiny n.
            if (view_wrap_config_is_effectively_bare(view_cfg, n_positions)) {
                run_empty_test(proofs, propagator);
                run_circuit_test(proofs, view_cfg, 1, propagator);
                run_circuit_test(proofs, view_cfg, 2, propagator);
                // n = 1 as well: the self-loop is the one solution, and it is the
                // smallest case where a negative value could reach as_index().
                run_circuit_wide_domain_test(proofs, 1, propagator);
                run_circuit_wide_domain_test(proofs, 4, propagator);
            }
        }
    }

    if (view_wrap_config_is_effectively_bare(view_cfg, n_positions))
        for (bool fixed : {true, false})
            if (! run_long_ring_test(fixed))
                return EXIT_FAILURE;

    return EXIT_SUCCESS;
}
