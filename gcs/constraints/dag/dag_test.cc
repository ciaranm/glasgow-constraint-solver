#include <gcs/constraints/dag.hh>
#include <gcs/constraints/dag/mutations.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
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
using std::optional;
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

    // What the constraint means: a selected edge has both endpoints selected, and
    // the selected edges hold no directed cycle. Note that this is stricter than
    // MiniZinc's own decomposition, which only forces an edge's head; see the
    // class documentation.
    auto satisfies(const Edges & edges, const vector<int> & ns, const vector<int> & es) -> bool
    {
        for (size_t e = 0; e != edges.size(); ++e)
            if (es[e] && (! ns[edges[e].first] || ! ns[edges[e].second]))
                return false;

        // Depth-first search, colouring grey on the way down: a grey node reached
        // again is a back edge, which is a cycle.
        auto n = ns.size();
        vector<int> colour(n, 0);
        auto visit = [&](auto && self, size_t v) -> bool {
            colour[v] = 1;
            for (size_t e = 0; e != edges.size(); ++e)
                if (es[e] && edges[e].first == v) {
                    auto w = edges[e].second;
                    if (colour[w] == 1)
                        return false;
                    if (colour[w] == 0 && ! self(self, w))
                        return false;
                }
            colour[v] = 2;
            return true;
        };
        for (size_t v = 0; v != n; ++v)
            if (colour[v] == 0 && ! visit(visit, v))
                return false;
        return true;
    }
}

auto run_dag_test(bool proofs, const string & name, const Edges & edges, const Ranges & ns_ranges, const Ranges & es_ranges) -> void
{
    print(cerr, "dag {} ns={} es={}{}", name, ns_ranges, es_ranges, proofs ? " with proofs:" : ":");
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
    p.post(Dag{edges, ns, es});

    // Generalised arc consistency, and not by accident: acyclicity is downward
    // closed, so leaving every undecided edge out gives every remaining value a
    // support unless putting the edge in would close a cycle, which is the one
    // thing the propagator checks.
    auto proof_name = proofs ? make_optional("dag_test_" + name) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{ns, es});

    check_results(proof_name, expected, actual);
}

// Aliasing: the same handle used for two nodes means those nodes are selected
// together. Consistency is not checked on a dup run, as elsewhere.
auto run_dup_dag_test(bool proofs, const Edges & edges, size_t num_nodes, const vector<size_t> & node_of_position) -> void
{
    print(cerr, "dag dup edges={} positions={}{}", edges, node_of_position, proofs ? " with proofs:" : ":");
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
    p.post(Dag{edges, ns, es});

    auto proof_name = proofs ? make_optional(string("dag_test_dup")) : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{unique_ns, es});
    check_results(proof_name, expected, actual);
}

// The mutation fixture. It has to make both shapes of inference, and it has to
// make them where a corrupted reason has nothing else to fall back on:
//
//   * the cycle is long enough that dropping one of its edges leaves a path
//     rather than a cycle, so the encoding really is asked to believe something
//     false. On a two cycle, dropping one edge leaves the other, and "this one
//     edge is selected" plus a solution-exclusion clause can be enough;
//
//   * there are two cycles sharing a node, so a dropped literal cannot be
//     recovered from the other cycle's rows;
//
//   * a node is only reachable through one edge, so the subgraph inferences fire
//     in both directions and dropping the endpoint literal leaves the RUP with
//     no support at all.
//
// A lane that verifies anyway is a finding about the honest reason, not about
// the test.
auto run_mutation(gcs::innards::dag::DagProofMutation mutation, const string & proof_basename) -> void
{
    Problem p;
    vector<IntegerVariableID> ns, es;
    for (int i = 0; i < 6; ++i)
        ns.push_back(p.create_integer_variable(0_i, 1_i, "n" + std::to_string(i)));

    // Two triangles, 0 -> 1 -> 2 -> 0 and 2 -> 3 -> 4 -> 2, sharing node 2, plus
    // a spur 4 -> 5 that no cycle can use.
    Edges edges{{0, 1}, {1, 2}, {2, 0}, {2, 3}, {3, 4}, {4, 2}, {4, 5}};
    for (size_t e = 0; e != edges.size(); ++e)
        es.push_back(p.create_integer_variable(0_i, 1_i, "e" + std::to_string(e)));

    p.post(Dag{edges, ns, es}.with_proof_mutation(mutation));

    solve_with(p, SolveCallbacks{.solution = [](const CurrentState &) { return true; }}, make_optional(ProofOptions{proof_basename}));
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    {
        using namespace gcs::innards::dag;
        optional<DagProofMutation> mutation;
        string proof_basename = "dag_mutation";
        for (int a = 1; a < argc; ++a) {
            string arg = argv[a];
            if (arg == "--mutate=path")
                mutation = dag_proof_mutation::DropPathEdge{};
            else if (arg == "--mutate=endpoint")
                mutation = dag_proof_mutation::DropEndpointLiteral{};
            else if (arg == "--mutate=none")
                mutation = dag_proof_mutation::None{};
            else if (arg == "--proof-files-basename" && a + 1 < argc)
                proof_basename = argv[++a];
        }
        if (mutation) {
            run_mutation(*mutation, proof_basename);
            if (std::holds_alternative<dag_proof_mutation::None>(*mutation))
                println(cerr, "wrote an unmutated proof of the mutation fixture to {}.pbp", proof_basename);
            else
                println(cerr, "wrote a deliberately corrupted proof to {}.pbp", proof_basename);
            return EXIT_SUCCESS;
        }
    }

    auto free = [](size_t n) { return Ranges(n, pair{0, 1}); };

    // A directed path, a triangle, a graph whose only cycle needs three edges, a
    // pair of triangles sharing a node, two components joined by an edge that no
    // cycle can use, a two cycle, and a self loop.
    const Edges path3{{0, 1}, {1, 2}};
    const Edges triangle{{0, 1}, {1, 2}, {2, 0}};
    const Edges diamond{{0, 1}, {0, 2}, {1, 3}, {2, 3}, {3, 0}};
    const Edges bowtie{{0, 1}, {1, 2}, {2, 0}, {2, 3}, {3, 4}, {4, 2}};
    const Edges two_pieces{{0, 1}, {1, 0}, {2, 3}, {3, 2}, {1, 2}};
    const Edges two_cycle{{0, 1}, {1, 0}};
    const Edges loop_and_parallel{{0, 0}, {0, 1}, {0, 1}};

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;

        run_dag_test(proofs, "empty", Edges{}, free(2), free(0));

        // Already acyclic, so the constraint has no levels to write at all and is
        // exactly Subgraph.
        run_dag_test(proofs, "path3", path3, free(3), free(2));

        run_dag_test(proofs, "triangle", triangle, free(3), free(3));
        run_dag_test(proofs, "diamond", diamond, free(4), free(5));
        run_dag_test(proofs, "bowtie", bowtie, free(5), free(6));
        run_dag_test(proofs, "two_pieces", two_pieces, free(4), free(5));
        run_dag_test(proofs, "two_cycle", two_cycle, free(2), free(2));

        // A self loop is a cycle of one, ruled out with no reason to give, and a
        // pair of parallel edges is not a cycle at all.
        run_dag_test(proofs, "loop_and_parallel", loop_and_parallel, free(2), free(3));

        // Edges and nodes pinned, so the propagator has to infer rather than just
        // check: two thirds of a triangle in makes the third impossible, and a node
        // out kills the edges at it.
        run_dag_test(proofs, "triangle_two_in", triangle, free(3), Ranges{1, 1, pair{0, 1}});
        run_dag_test(proofs, "bowtie_node_out", bowtie, Ranges{pair{0, 1}, pair{0, 1}, 0, pair{0, 1}, pair{0, 1}}, free(6));

        // A constant everywhere, which is the shape the maximum acyclic subgraph
        // model has: every node in, only the edges to choose.
        run_dag_test(proofs, "bowtie_all_nodes_in", bowtie, Ranges{1, 1, 1, 1, 1}, free(6));

        run_dup_dag_test(proofs, triangle, 2, {0, 1, 0});
    }

    return EXIT_SUCCESS;
}
