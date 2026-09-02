#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/path.hh>
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

    // What the constraint means, written as a walk rather than as the degree
    // counting the implementation posts, so that the two are independent: start at
    // `start`, follow the one selected edge available at each step, and insist on
    // arriving at `end` having used every selected edge and visited every selected
    // node. A branch, a revisit or a leftover edge is not a path.
    auto satisfies(const Edges & edges, bool directed, int start, int end, const vector<int> & ns, const vector<int> & es) -> bool
    {
        if (start < 0 || std::cmp_greater_equal(start, ns.size()) || end < 0 || std::cmp_greater_equal(end, ns.size()))
            return false;

        for (size_t e = 0; e != edges.size(); ++e)
            if (es[e] && (! ns[edges[e].first] || ! ns[edges[e].second]))
                return false;

        if (! ns[static_cast<size_t>(start)] || ! ns[static_cast<size_t>(end)])
            return false;

        auto num_selected_edges = 0;
        for (auto e : es)
            num_selected_edges += e;

        vector<bool> visited(ns.size(), false);
        auto current = static_cast<size_t>(start);
        visited[current] = true;
        auto used = 0;
        auto came_in_on = edges.size();
        while (true) {
            // Every way onwards from here, not counting the edge just walked. More
            // than one is a branch, which a path does not have.
            vector<pair<size_t, size_t>> onwards;
            for (size_t e = 0; e != edges.size(); ++e) {
                if (! es[e] || e == came_in_on)
                    continue;
                if (edges[e].first == current)
                    onwards.emplace_back(e, edges[e].second);
                else if (! directed && edges[e].second == current)
                    onwards.emplace_back(e, edges[e].first);
            }
            if (onwards.size() > 1)
                return false;
            if (onwards.empty())
                break;
            auto [e, next] = onwards.front();
            if (visited[next])
                return false;
            visited[next] = true;
            came_in_on = directed ? edges.size() : e;
            current = next;
            ++used;
        }

        if (current != static_cast<size_t>(end))
            return false;
        if (used != num_selected_edges)
            return false;
        for (size_t v = 0; v != ns.size(); ++v)
            if (ns[v] != (visited[v] ? 1 : 0))
                return false;
        return true;
    }

    auto post(Problem & p, bool directed, Edges edges, IntegerVariableID start, IntegerVariableID end, vector<IntegerVariableID> ns,
        vector<IntegerVariableID> es) -> void
    {
        if (directed)
            p.post(DPath{std::move(edges), start, end, std::move(ns), std::move(es)});
        else
            p.post(Path{std::move(edges), start, end, std::move(ns), std::move(es)});
    }
}

auto run_path_test(bool proofs, bool directed, const string & name, const Edges & edges, const Ranges & ns_ranges, const Ranges & es_ranges,
    variant<int, pair<int, int>> start_range, variant<int, pair<int, int>> end_range) -> void
{
    print(cerr, "{} {} start={} end={} ns={} es={}{}", directed ? "dpath" : "path", name, start_range, end_range, ns_ranges, es_ranges,
        proofs ? " with proofs:" : ":");
    cerr << flush;

    set<tuple<int, int, vector<int>, vector<int>>> expected, actual;
    build_expected(
        expected, [&](int start, int end, const vector<int> & ns, const vector<int> & es) { return satisfies(edges, directed, start, end, ns, es); },
        start_range, end_range, ns_ranges, es_ranges);
    println(cerr, " expecting {} solutions", expected.size());

    Problem p;
    auto start = visit([&](auto r) { return create_integer_variable_or_constant(p, r); }, start_range);
    auto end = visit([&](auto r) { return create_integer_variable_or_constant(p, r); }, end_range);
    vector<IntegerVariableID> ns, es;
    for (const auto & r : ns_ranges)
        ns.push_back(visit([&](auto d) { return create_integer_variable_or_constant(p, d); }, r));
    for (const auto & r : es_ranges)
        es.push_back(visit([&](auto d) { return create_integer_variable_or_constant(p, d); }, r));
    post(p, directed, edges, start, end, ns, es);

    // Not the GAC check; see Tree.
    auto proof_name = proofs ? make_optional("path_test_" + string(directed ? "d" : "u") + "_" + name) : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{start, end, ns, es});

    check_results(proof_name, expected, actual);
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    auto free = [](size_t n) { return Ranges(n, pair{0, 1}); };

    const Edges path3{{0, 1}, {1, 2}};
    const Edges triangle{{0, 1}, {1, 2}, {0, 2}};
    const Edges square{{0, 1}, {1, 3}, {3, 2}, {2, 0}};
    const Edges two_pieces{{0, 1}, {2, 3}};
    const Edges lollipop{{0, 1}, {1, 2}, {2, 0}, {2, 3}};
    const Edges antiparallel{{0, 1}, {1, 0}, {1, 2}};
    const Edges loop_and_parallel{{0, 0}, {0, 1}, {0, 1}};

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;

        for (bool directed : {false, true}) {
            run_path_test(proofs, directed, "single", Edges{}, free(1), free(0), pair{0, 0}, pair{0, 0});
            run_path_test(proofs, directed, "path3", path3, free(3), free(2), pair{0, 2}, pair{0, 2});
            run_path_test(proofs, directed, "triangle", triangle, free(3), free(3), pair{0, 2}, pair{0, 2});
            run_path_test(proofs, directed, "square", square, free(4), free(4), pair{0, 3}, pair{0, 3});
            run_path_test(proofs, directed, "two_pieces", two_pieces, free(4), free(2), pair{0, 3}, pair{0, 3});
            run_path_test(proofs, directed, "lollipop", lollipop, free(4), free(4), pair{0, 3}, pair{0, 3});
            run_path_test(proofs, directed, "antiparallel", antiparallel, free(3), free(3), pair{0, 2}, pair{0, 2});

            // A self loop and parallel edges, neither of which a path can use: the
            // loop counts twice towards its node's degree, and taking both parallel
            // edges would revisit a node.
            run_path_test(proofs, directed, "loop_and_parallel", loop_and_parallel, free(2), free(3), pair{0, 1}, pair{0, 1});

            // start = end, the case where "at most one edge at each end" is not
            // enough on its own and the subgraph has to collapse to one node.
            run_path_test(proofs, directed, "path3_same_ends", path3, free(3), free(2), 1, 1);
            run_path_test(proofs, directed, "triangle_same_ends", triangle, free(3), free(3), 0, 0);

            // Both endpoints fixed and different, which is how dpath is usually
            // called, and one endpoint fixed with the other free.
            run_path_test(proofs, directed, "square_0_to_3", square, free(4), free(4), 0, 3);
            run_path_test(proofs, directed, "lollipop_from0", lollipop, free(4), free(4), 0, pair{0, 3});

            // Pinned nodes and edges, so the degree rules have something to say
            // before search decides everything.
            run_path_test(proofs, directed, "square_edges", square, free(4), Ranges{1, pair{0, 1}, pair{0, 1}, 0}, pair{0, 3}, pair{0, 3});
            run_path_test(proofs, directed, "lollipop_node_out", lollipop, Ranges{pair{0, 1}, pair{0, 1}, pair{0, 1}, 0}, free(4), 0, pair{0, 3});

            // Endpoints declared wider than the node numbering.
            run_path_test(proofs, directed, "path3_wide_ends", path3, free(3), free(2), pair{-1, 3}, pair{0, 3});
        }
    }

    return EXIT_SUCCESS;
}
