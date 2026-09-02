#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/subgraph.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstddef>
#include <cstdlib>
#include <iostream>
#include <optional>
#include <set>
#include <string>
#include <tuple>
#include <utility>
#include <variant>
#include <vector>

using std::cerr;
using std::flush;
using std::make_optional;
using std::nullopt;
using std::pair;
using std::set;
using std::size_t;
using std::string;
using std::tuple;
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

namespace
{
    using Edges = vector<pair<size_t, size_t>>;
    using Ranges = vector<variant<int, pair<int, int>>>;

    // What the constraint means: a selected edge has both endpoints selected.
    // Nothing requires a node to be in an edge, so all-zero is a solution.
    auto satisfies(const Edges & edges, const vector<int> & ns, const vector<int> & es) -> bool
    {
        for (size_t e = 0; e != edges.size(); ++e)
            if (es[e] && (! ns[edges[e].first] || ! ns[edges[e].second]))
                return false;
        return true;
    }
}

auto run_subgraph_test(bool proofs, const string & name, const Edges & edges, const Ranges & ns_ranges, const Ranges & es_ranges) -> void
{
    print(cerr, "subgraph {} ns={} es={}{}", name, ns_ranges, es_ranges, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<vector<int>, vector<int>>> expected, actual;
    build_expected(expected, [&](const vector<int> & ns, const vector<int> & es) { return satisfies(edges, ns, es); }, ns_ranges, es_ranges);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> ns, es;
    for (const auto & r : ns_ranges)
        ns.push_back(visit([&](auto d) { return create_integer_variable_or_constant(p, d); }, r));
    for (const auto & r : es_ranges)
        es.push_back(visit([&](auto d) { return create_integer_variable_or_constant(p, d); }, r));
    p.post(Subgraph{edges, ns, es});

    // Two implications per edge, propagated in both directions, so this really is
    // generalised-arc-consistent: at a fixpoint, every remaining value extends to a
    // solution by putting every undecided node in and leaving every undecided edge
    // out.
    auto proof_name = proofs ? make_optional("subgraph_test_" + name) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{ns, es});

    check_results(proof_name, expected, actual);
}

// Aliasing: the same handle used for two nodes means those nodes are selected
// together. Consistency is not checked on a dup run, as elsewhere.
auto run_dup_subgraph_test(bool proofs, const Edges & edges, size_t num_nodes, const vector<size_t> & node_of_position) -> void
{
    print(cerr, "subgraph dup edges={} positions={}{}", edges, node_of_position, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<vector<int>, vector<int>>> expected, actual;
    build_expected(
        expected,
        [&](const vector<int> & unique_ns, const vector<int> & es) {
            vector<int> ns;
            for (auto n : node_of_position)
                ns.push_back(unique_ns.at(n));
            return satisfies(edges, ns, es);
        },
        vector<pair<int, int>>(num_nodes, pair{0, 1}), vector<pair<int, int>>(edges.size(), pair{0, 1}));
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    vector<IntegerVariableID> unique_ns;
    for (size_t i = 0; i != num_nodes; ++i)
        unique_ns.push_back(p.create_integer_variable(0_i, 1_i));
    vector<IntegerVariableID> ns;
    for (auto n : node_of_position)
        ns.push_back(unique_ns.at(n));
    vector<IntegerVariableID> es;
    for (size_t e = 0; e != edges.size(); ++e)
        es.push_back(p.create_integer_variable(0_i, 1_i));
    p.post(Subgraph{edges, ns, es});

    auto proof_name = proofs ? make_optional(string("subgraph_test_dup")) : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{unique_ns, es});
    check_results(proof_name, expected, actual);
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    auto free = [](size_t n) { return Ranges(n, pair{0, 1}); };

    const Edges path3{{0, 1}, {1, 2}};
    const Edges triangle{{0, 1}, {1, 2}, {0, 2}};
    const Edges loop_and_parallel{{0, 0}, {0, 1}, {0, 1}};

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;

        run_subgraph_test(proofs, "empty", Edges{}, free(2), free(0));
        run_subgraph_test(proofs, "path3", path3, free(3), free(2));
        run_subgraph_test(proofs, "triangle", triangle, free(3), free(3));

        // A self loop and a pair of parallel edges: both are ordinary edges here,
        // and the endpoint rows do not care that they repeat.
        run_subgraph_test(proofs, "loop_and_parallel", loop_and_parallel, free(2), free(3));

        // Nodes and edges pinned, so each direction of the implication has
        // something to say: an edge in forces its endpoints, and a node out kills
        // its edges.
        run_subgraph_test(proofs, "path3_edge_in", path3, free(3), Ranges{1, pair{0, 1}});
        run_subgraph_test(proofs, "path3_node_out", path3, Ranges{pair{0, 1}, 0, pair{0, 1}}, free(2));

        run_dup_subgraph_test(proofs, path3, 2, {0, 1, 0});
    }

    return EXIT_SUCCESS;
}
