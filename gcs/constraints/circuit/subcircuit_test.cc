#include <gcs/constraints/circuit.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/exception.hh>
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

// A successor assignment is a subcircuit iff it is a permutation and the nodes that do
// not point at themselves form at most one cycle. Written straight off MiniZinc's
// definition, including its two corners: every node pointing at itself (the empty
// subcircuit) is a solution, and the smallest non-empty tour has two nodes, because a
// node pointing at itself is by definition off the tour.
auto is_subcircuit(const vector<int> & succ) -> bool
{
    auto n = succ.size();

    vector<bool> used(n, false);
    for (auto v : succ) {
        if (v < 0 || std::cmp_greater_equal(v, n))
            return false;
        if (used[static_cast<std::size_t>(v)])
            return false;
        used[static_cast<std::size_t>(v)] = true;
    }

    vector<bool> seen(n, false);
    auto tours = 0;
    for (std::size_t i = 0; i < n; ++i) {
        if (seen[i])
            continue;
        auto j = i;
        std::size_t length = 0;
        do {
            seen[j] = true;
            j = static_cast<std::size_t>(succ[j]);
            ++length;
        } while (j != i);
        if (length >= 2)
            ++tours;
    }

    return tours <= 1;
}

enum struct SubCircuitPropagator
{
    check,
    prevent
};

auto run_subcircuit_test(bool proofs, const ViewWrapConfig & view_cfg, int n, SubCircuitPropagator propagator) -> void
{
    auto wraps = wraps_for_positions(view_cfg, n);
    auto prop_label = propagator == SubCircuitPropagator::prevent ? "prevent" : "check";
    print(cerr, "subcircuit/{} [{}] n={}{}", prop_label, view_wrap_config_label(view_cfg), n, proofs ? " with proofs:" : ":");
    cerr << flush;

    vector<pair<int, int>> domains(static_cast<std::size_t>(n), pair{0, n - 1});

    set<tuple<vector<int>>> expected, actual;
    build_expected(expected, [&](vector<int> succ) { return is_subcircuit(succ); }, domains);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> succ;
    for (int i = 0; i < n; ++i)
        succ.push_back(create_integer_variable_or_constant_with_view(p, pair{0, n - 1}, wraps.at(static_cast<std::size_t>(i))));
    if (propagator == SubCircuitPropagator::prevent)
        p.post(SubCircuit{succ}.with_algorithm(subcircuit::Prevent{}));
    else
        p.post(SubCircuit{succ}.with_algorithm(subcircuit::Check{}));

    // Not solve_for_tests_checking_gac: neither algorithm claims arc consistency. Both
    // wait for a chain of successors to be fixed before they say anything at all, so a
    // value can easily survive in a domain with no solution behind it.
    //
    // This is also the test that keeps derive_tour_at_most() honest, from n = 5 up: swap it
    // for a plain JustifyUsingRUP and VeriPB rejects the proof here. It did not used to be
    // -- while off-tour positions were numbered after the on-tour ones, unit propagation
    // could reach the conflict unaided at these sizes, and only a scenario with the anchor
    // left undetermined could tell the difference. Pinning off-tour positions to zero made
    // the cheap test the one that catches it, which is where that check wants to live.
    auto proof_name = proofs ? make_optional("subcircuit_test_" + std::string{prop_label} + "_" + view_wrap_config_label(view_cfg)) : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{succ});
    check_results(proof_name, expected, actual);
}

// The empty successor array. MiniZinc's own definition special-cases it to `true`, so we
// are never handed one from there, but a C++ caller can build one out of a loop bound and
// it should be a no-op rather than a crash: there is no node to be on a tour or off it.
auto run_empty_test(bool proofs) -> void
{
    println(cerr, "subcircuit/empty{}", proofs ? " with proofs:" : ":");

    Problem p;
    auto witness = p.create_integer_variable(0_i, 1_i);
    p.post(SubCircuit{vector<IntegerVariableID>{}});

    auto proof_name = proofs ? make_optional<std::string>("subcircuit_test_empty") : nullopt;
    set<tuple<vector<int>>> expected{tuple{vector<int>{0}}, tuple{vector<int>{1}}}, actual;
    solve_for_tests(p, proof_name, actual, tuple{vector<IntegerVariableID>{witness}});
    check_results(proof_name, expected, actual);
}

// The tour size, XCSP3's `size` argument. Enumerated against the same reference check with
// the count computed alongside it, so the option is pinned to "how many nodes do not point
// at themselves" and not to some off-by-one reading of it.
auto run_tour_size_test(bool proofs, int n, int size_lower, int size_upper) -> void
{
    println(cerr, "subcircuit/tour_size n={} size={}..{}{}", n, size_lower, size_upper, proofs ? " with proofs:" : ":");

    vector<pair<int, int>> domains(static_cast<std::size_t>(n) + 1, pair{0, n - 1});
    domains.back() = pair{size_lower, size_upper};

    set<tuple<vector<int>>> expected, actual;
    build_expected(
        expected,
        [&](vector<int> all) {
            auto succ = vector<int>(all.begin(), all.end() - 1);
            if (! is_subcircuit(succ))
                return false;
            auto on = 0;
            for (std::size_t i = 0; i < succ.size(); ++i)
                if (succ[i] != static_cast<int>(i))
                    ++on;
            return on == all.back();
        },
        domains);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> succ;
    for (int i = 0; i < n; ++i)
        succ.push_back(p.create_integer_variable(0_i, Integer{n - 1}));
    auto size = p.create_integer_variable(Integer{size_lower}, Integer{size_upper});
    p.post(SubCircuit{succ}.with_tour_size(size));

    auto all_vars = succ;
    all_vars.emplace_back(size);
    auto proof_name = proofs ? make_optional<std::string>("subcircuit_test_tour_size") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{all_vars});
    check_results(proof_name, expected, actual);
}

// The anchored encoding: same constraint, half the rows, and one polish-notation step per
// certificate instead of one per node of the cycle. Enumerated against the same reference
// check, restricted to the solutions where the named node is on the tour, since that is the
// precondition the caller has to have declared.
auto run_anchored_test(bool proofs, int n, int anchor) -> void
{
    println(cerr, "subcircuit/anchored n={} anchor={}{}", n, anchor, proofs ? " with proofs:" : ":");

    vector<pair<int, int>> domains(static_cast<std::size_t>(n), pair{0, n - 1});

    set<tuple<vector<int>>> expected, actual;
    build_expected(expected, [&](vector<int> succ) { return is_subcircuit(succ) && succ[static_cast<std::size_t>(anchor)] != anchor; }, domains);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> succ;
    for (int i = 0; i < n; ++i) {
        // The anchor's own index has to be out of its declared domain: with_required_node()
        // takes that as a precondition rather than imposing it, so that the constraint means
        // the same thing either way and nothing about it has to reach the .scp.
        vector<Integer> values;
        for (int v = 0; v < n; ++v)
            if (! (i == anchor && v == anchor))
                values.emplace_back(Integer{v});
        succ.push_back(p.create_integer_variable(values));
    }
    p.post(SubCircuit{succ}.with_required_node(anchor));

    auto proof_name = proofs ? make_optional<std::string>("subcircuit_test_anchored") : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{succ});
    check_results(proof_name, expected, actual);
}

// with_required_node() is a precondition, so it has to say so rather than quietly building
// an unsound encoding: the anchored rows force the tour's length to zero if the named node
// turns out to be off it. The range is checked at the call, the domain when the constraint
// is installed -- post() only stores it -- so the two are caught in different places.
auto run_anchor_rejection_tests() -> bool
{
    auto ok = true;

    {
        Problem p;
        auto x = p.create_integer_variable_vector(4, 0_i, 3_i);
        try {
            SubCircuit{x}.with_required_node(4);
            println(cerr, "out-of-range anchor: expected InvalidProblemDefinitionException from with_required_node");
            ok = false;
        }
        catch (const InvalidProblemDefinitionException &) {
        }
    }

    {
        Problem p;
        auto x = p.create_integer_variable_vector(4, 0_i, 3_i);
        p.post(SubCircuit{x}.with_required_node(2));
        try {
            solve_with(p, SolveCallbacks{});
            println(cerr, "anchor still able to be a self loop: expected InvalidProblemDefinitionException from the solve");
            ok = false;
        }
        catch (const InvalidProblemDefinitionException &) {
        }
    }

    return ok;
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    // Instances run at n = 3, 4, 5; positions 0..4 cover the largest fully. n = 4 is the
    // smallest size that says anything beyond all-different: with three nodes every
    // permutation is a subcircuit, since two disjoint cycles need four nodes between them.
    constexpr int n_positions = 5;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        println(cerr, "subcircuit view sweep: position {} out of range for n_positions = {}; skipping", *view_cfg.single_position, n_positions);
        return EXIT_SUCCESS;
    }

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;
        for (auto propagator : {SubCircuitPropagator::check, SubCircuitPropagator::prevent}) {
            for (int n : {3, 4, 5})
                run_subcircuit_test(proofs, view_cfg, n, propagator);
            // The degenerate sizes: n=1 has only the empty subcircuit, n=2 has the empty
            // one and the single 2-cycle. Bare configuration only, as circuit_test does:
            // the view sweep's positions can exceed these tiny n.
            if (view_wrap_config_is_effectively_bare(view_cfg, n_positions)) {
                run_subcircuit_test(proofs, view_cfg, 1, propagator);
                run_subcircuit_test(proofs, view_cfg, 2, propagator);
            }
        }
        if (view_wrap_config_is_effectively_bare(view_cfg, n_positions)) {
            run_empty_test(proofs);
            // The full range, so the option constrains nothing and every subcircuit
            // survives with its own count; then a lower bound of 2, which is how XCSP3's
            // "exactly one circuit" reading is spelled and rules the empty tour out; then
            // an exact size, and 1, which nothing can satisfy because a lone node on the
            // tour has nowhere to point but itself.
            for (int n : {3, 4, 5})
                for (int anchor : {0, n - 1})
                    run_anchored_test(proofs, n, anchor);
            for (int n : {3, 4}) {
                run_tour_size_test(proofs, n, 0, n);
                run_tour_size_test(proofs, n, 2, n);
                run_tour_size_test(proofs, n, n, n);
                run_tour_size_test(proofs, n, 1, 1);
            }
        }
    }

    if (view_wrap_config_is_effectively_bare(view_cfg, n_positions) && ! run_anchor_rejection_tests())
        return EXIT_FAILURE;

    return EXIT_SUCCESS;
}
