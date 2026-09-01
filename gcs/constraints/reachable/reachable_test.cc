#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/reachable.hh>
#include <gcs/constraints/reachable/mutations.hh>
#include <gcs/current_state.hh>
#include <gcs/problem.hh>
#include <gcs/proof.hh>
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

    // What the constraint means, written out directly: every selected edge has both
    // endpoints selected, the root is selected, and every selected node is reached
    // from the root along selected edges.
    auto satisfies(const Edges & edges, bool directed, int root, const vector<int> & ns, const vector<int> & es) -> bool
    {
        // A root that is not a node number cannot be selected, so it is simply false.
        if (root < 0 || std::cmp_greater_equal(root, ns.size()))
            return false;

        for (size_t e = 0; e != edges.size(); ++e)
            if (es[e] && (! ns[edges[e].first] || ! ns[edges[e].second]))
                return false;

        if (! ns[static_cast<size_t>(root)])
            return false;

        vector<bool> seen(ns.size(), false);
        vector<size_t> stack{static_cast<size_t>(root)};
        seen[static_cast<size_t>(root)] = true;
        while (! stack.empty()) {
            auto v = stack.back();
            stack.pop_back();
            for (size_t e = 0; e != edges.size(); ++e) {
                if (! es[e])
                    continue;
                for (auto [from, to] : {pair{edges[e].first, edges[e].second}, pair{edges[e].second, edges[e].first}}) {
                    if (directed && from != edges[e].first)
                        continue;
                    if (from == v && ! seen[to]) {
                        seen[to] = true;
                        stack.push_back(to);
                    }
                }
            }
        }

        for (size_t v = 0; v != ns.size(); ++v)
            if (ns[v] && ! seen[v])
                return false;
        return true;
    }

    auto post(Problem & p, bool directed, Edges edges, IntegerVariableID root, vector<IntegerVariableID> ns, vector<IntegerVariableID> es) -> void
    {
        if (directed)
            p.post(DReachable{std::move(edges), root, std::move(ns), std::move(es)});
        else
            p.post(Reachable{std::move(edges), root, std::move(ns), std::move(es)});
    }
}

auto run_reachable_test(bool proofs, bool directed, const string & name, const Edges & edges, const Ranges & ns_ranges, const Ranges & es_ranges,
    variant<int, pair<int, int>> root_range) -> void
{
    print(cerr, "{} {} root={} ns={} es={}{}", directed ? "dreachable" : "reachable", name, root_range, ns_ranges, es_ranges,
        proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, vector<int>, vector<int>>> expected, actual;
    build_expected(
        expected, [&](int root, const vector<int> & ns, const vector<int> & es) { return satisfies(edges, directed, root, ns, es); }, root_range,
        ns_ranges, es_ranges);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto root = visit([&](auto r) { return create_integer_variable_or_constant(p, r); }, root_range);
    vector<IntegerVariableID> ns, es;
    for (const auto & r : ns_ranges)
        ns.push_back(visit([&](auto d) { return create_integer_variable_or_constant(p, d); }, r));
    for (const auto & r : es_ranges)
        es.push_back(visit([&](auto d) { return create_integer_variable_or_constant(p, d); }, r));
    post(p, directed, edges, root, ns, es);

    // The GAC check, and it passes for both spellings: with the cut-vertex and
    // bridge forcing on, this propagator is generalised-arc-consistent, so every
    // value left in every domain at every search node has a support. That is the
    // check earning its keep rather than a claim --- before the forcing was added
    // it failed here, on `path3` at root 0 with nodes 0 and 1 selected, where edge
    // (0, 1) is the only way to join two selected nodes. Note that the forcing is
    // about the *residual* graph, which is why the 2-connected `triangle` case
    // failed too once a node had been excluded. See
    // dev_docs/connectivity-proofs.md.
    auto proof_name = proofs ? make_optional("reachable_test_" + string(directed ? "d" : "u") + "_" + name) : nullopt;
    solve_for_tests_checking_gac(p, proof_name, expected, actual, tuple{root, ns, es});

    check_results(proof_name, expected, actual);
}

// Aliasing: the same handle used for two nodes means those nodes are selected
// together. The propagator reads state per node, so it copes; consistency is not
// checked on a dup run, as elsewhere.
auto run_dup_reachable_test(bool proofs, bool directed, const Edges & edges, size_t num_nodes, const vector<size_t> & node_of_position) -> void
{
    print(cerr, "{} dup edges={} positions={}{}", directed ? "dreachable" : "reachable", edges, node_of_position, proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, vector<int>, vector<int>>> expected, actual;
    build_expected(
        expected,
        [&](int root, const vector<int> & unique_ns, const vector<int> & es) {
            vector<int> ns;
            for (auto n : node_of_position)
                ns.push_back(unique_ns.at(n));
            return satisfies(edges, directed, root, ns, es);
        },
        pair{0, static_cast<int>(node_of_position.size()) - 1}, vector<pair<int, int>>(num_nodes, pair{0, 1}),
        vector<pair<int, int>>(edges.size(), pair{0, 1}));
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto root = p.create_integer_variable(0_i, Integer(static_cast<long long>(node_of_position.size()) - 1));
    vector<IntegerVariableID> unique_ns;
    for (size_t i = 0; i != num_nodes; ++i)
        unique_ns.push_back(p.create_integer_variable(0_i, 1_i));
    vector<IntegerVariableID> ns;
    for (auto n : node_of_position)
        ns.push_back(unique_ns.at(n));
    vector<IntegerVariableID> es;
    for (size_t e = 0; e != edges.size(); ++e)
        es.push_back(p.create_integer_variable(0_i, 1_i));
    post(p, directed, edges, root, ns, es);

    auto proof_name = proofs ? make_optional(string("reachable_test_dup_") + (directed ? "d" : "u")) : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{root, unique_ns, es});
    check_results(proof_name, expected, actual);
}

// Mutation mode: enumerate the fixture below with a deliberately corrupted
// reason and stop, for run_test_and_expect_verify_failure.bash to hand to
// veripb.
//
// The fixture is six free nodes, enumerated. Two things about it were arrived at
// the hard way, and both are the "margin of one" discipline in
// dev_docs/constraints.md:
//
//   * everything is free rather than pinned. A node pinned out in the *model* is
//     pinned in the OPB too, so unit propagation has it without being told, and
//     dropping it from a reason changes nothing. A first attempt pinned two
//     nodes, and the mandatory and root-domain lanes both verified for exactly
//     that reason. Under search the same facts are decisions, so a reason that
//     does not carry them is one veripb cannot replay.
//
//   * the graph both forks and cycles. Enumeration leaves a solution-exclusion
//     clause alive for every solution already found, and those clauses are what
//     a corrupted reason falls back on. On a directed path, the chosen root plus
//     an exclusion clause pin the single node downstream of it --- which is
//     exactly the node the mandatory literal names, so dropping it cost nothing
//     and that lane verified; the fork gives two nodes downstream and the clause
//     is no longer a unit. Symmetrically, a node whose only way in is one arc
//     has "the root is that node" as its only other support, which an exclusion
//     clause can also supply; the cycle gives the cut-off region more than one
//     way to be entered, so the root-domain literals have to be said out loud.
//     Each of those was a lane that verified before the shape was fixed.
//
// A lane that verifies anyway is a finding about the honest reason, not about
// the test.
auto run_mutation(bool directed, gcs::innards::reachable::ReachableProofMutation mutation, const string & proof_basename) -> void
{
    Problem p;
    auto root = p.create_integer_variable(0_i, 6_i, "root");
    vector<IntegerVariableID> ns, es;
    for (int i = 0; i < 7; ++i)
        ns.push_back(p.create_integer_variable(0_i, 1_i, "n" + std::to_string(i)));
    for (int e = 0; e < 7; ++e)
        es.push_back(p.create_integer_variable(0_i, 1_i, "e" + std::to_string(e)));

    // A path 0 - 1 - 2 - 3, a triangle 3 - 4 - 5 - 3 hanging off it, and a spur
    // 3 - 6. Read as arcs, that is a path into a directed cycle, with a fork.
    Edges edges{{0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 5}, {5, 3}, {3, 6}};
    if (directed)
        p.post(DReachable{edges, root, ns, es}.with_proof_mutation(mutation));
    else
        p.post(Reachable{edges, root, ns, es}.with_proof_mutation(mutation));

    solve_with(p, SolveCallbacks{.solution = [](const CurrentState &) { return true; }}, make_optional(ProofOptions{proof_basename}));
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    {
        using namespace gcs::innards::reachable;
        optional<ReachableProofMutation> mutation;
        auto directed = false;
        string proof_basename = "reachable_mutation";
        for (int a = 1; a < argc; ++a) {
            string arg = argv[a];
            if (arg == "--mutate=border")
                mutation = reachable_proof_mutation::DropBorderLiteral{};
            else if (arg == "--mutate=mandatory")
                mutation = reachable_proof_mutation::DropMandatoryNode{};
            else if (arg == "--mutate=rootdomain")
                mutation = reachable_proof_mutation::DropRootDomain{};
            else if (arg == "--mutate=none")
                mutation = reachable_proof_mutation::None{};
            else if (arg == "--directed")
                directed = true;
            else if (arg == "--proof-files-basename" && a + 1 < argc)
                proof_basename = argv[++a];
        }
        if (mutation) {
            run_mutation(directed, *mutation, proof_basename);
            if (std::holds_alternative<reachable_proof_mutation::None>(*mutation))
                println(cerr, "wrote an unmutated proof of the mutation fixture to {}.pbp", proof_basename);
            else
                println(cerr, "wrote a deliberately corrupted proof to {}.pbp", proof_basename);
            return EXIT_SUCCESS;
        }
    }

    auto free = [](size_t n) { return Ranges(n, pair{0, 1}); };

    // A path, a triangle, a square, a graph with a cut vertex and a bridge, and a
    // graph that is already in two pieces so nothing can join them.
    const Edges path3{{0, 1}, {1, 2}};
    const Edges triangle{{0, 1}, {1, 2}, {0, 2}};
    const Edges square{{0, 1}, {1, 3}, {3, 2}, {2, 0}};
    const Edges bowtie{{0, 1}, {1, 2}, {2, 0}, {2, 3}, {3, 4}, {4, 2}};
    const Edges two_pieces{{0, 1}, {2, 3}};
    const Edges lollipop{{0, 1}, {1, 2}, {2, 0}, {2, 3}};

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;

        for (bool directed : {false, true}) {
            run_reachable_test(proofs, directed, "single", Edges{}, free(1), free(0), pair{0, 0});
            run_reachable_test(proofs, directed, "path3", path3, free(3), free(2), pair{0, 2});
            run_reachable_test(proofs, directed, "triangle", triangle, free(3), free(3), pair{0, 2});
            run_reachable_test(proofs, directed, "square", square, free(4), free(4), pair{0, 3});
            run_reachable_test(proofs, directed, "two_pieces", two_pieces, free(4), free(2), pair{0, 3});
            run_reachable_test(proofs, directed, "lollipop", lollipop, free(4), free(4), pair{0, 3});

            // A fixed root, which is the shape `dreachable` is usually called with.
            run_reachable_test(proofs, directed, "path3_root0", path3, free(3), free(2), 0);
            run_reachable_test(proofs, directed, "bowtie_root0", bowtie, free(5), free(6), 0);

            // Nodes pinned in and out: the cut vertex 2 has to come in when 0 and 3
            // are both in, and nothing can reach past a node pinned out.
            run_reachable_test(proofs, directed, "lollipop_pinned", lollipop, Ranges{1, pair{0, 1}, pair{0, 1}, 1}, free(4), pair{0, 3});
            run_reachable_test(proofs, directed, "lollipop_cut_out", lollipop, Ranges{pair{0, 1}, pair{0, 1}, 0, pair{0, 1}}, free(4), pair{0, 3});

            // A root declared wider than the node numbering: the out-of-range
            // values are ruled out by the constraint rather than rejected.
            run_reachable_test(proofs, directed, "path3_wide_root", path3, free(3), free(2), pair{-1, 4});

            // Edges pinned, so the subgraph rules have something to say.
            run_reachable_test(proofs, directed, "square_edges", square, free(4), Ranges{1, pair{0, 1}, pair{0, 1}, 0}, pair{0, 3});

            run_dup_reachable_test(proofs, directed, path3, 2, {0, 1, 0});
        }
    }

    return EXIT_SUCCESS;
}
