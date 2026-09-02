#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/tree.hh>
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

    // What the constraint means, written out directly rather than as the
    // reachability-plus-counting the implementation posts: the selected subgraph
    // is a tree rooted at `root`. Undirected that is "connected and acyclic";
    // directed it is "every selected node is reached from the root by a unique
    // path", which is the same as acyclic with one edge into each non-root node.
    auto satisfies(const Edges & edges, bool directed, int root, const vector<int> & ns, const vector<int> & es) -> bool
    {
        if (root < 0 || std::cmp_greater_equal(root, ns.size()))
            return false;

        for (size_t e = 0; e != edges.size(); ++e)
            if (es[e] && (! ns[edges[e].first] || ! ns[edges[e].second]))
                return false;

        if (! ns[static_cast<size_t>(root)])
            return false;

        auto num_nodes = 0, num_edges = 0;
        for (auto n : ns)
            num_nodes += n;
        for (auto e : es)
            num_edges += e;
        if (num_edges != num_nodes - 1)
            return false;

        if (directed)
            for (size_t v = 0; v != ns.size(); ++v) {
                auto in = 0;
                for (size_t e = 0; e != edges.size(); ++e)
                    if (es[e] && edges[e].second == v)
                        ++in;
                if (in > 1)
                    return false;
            }

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
            p.post(DTree{std::move(edges), root, std::move(ns), std::move(es)});
        else
            p.post(Tree{std::move(edges), root, std::move(ns), std::move(es)});
    }
}

auto run_tree_test(bool proofs, bool directed, const string & name, const Edges & edges, const Ranges & ns_ranges, const Ranges & es_ranges,
    variant<int, pair<int, int>> root_range) -> void
{
    print(cerr, "{} {} root={} ns={} es={}{}", directed ? "dtree" : "tree", name, root_range, ns_ranges, es_ranges, proofs ? " with proofs:" : ":");
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

    // Not solve_for_tests_checking_gac, and deliberately: Reachable is GAC and the
    // cardinality equality is GAC, but their conjunction is not, which is the
    // general point dev_docs/constraints.md makes about decompositions. The
    // triangle at three free nodes is the smallest case that shows it --- with two
    // nodes in and one edge in, nothing here rules out a second edge until the
    // count is checked, though no solution uses one.
    auto proof_name = proofs ? make_optional("tree_test_" + string(directed ? "d" : "u") + "_" + name) : nullopt;
    solve_for_tests(p, proof_name, actual, tuple{root, ns, es});

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

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;

        for (bool directed : {false, true}) {
            run_tree_test(proofs, directed, "single", Edges{}, free(1), free(0), pair{0, 0});
            run_tree_test(proofs, directed, "path3", path3, free(3), free(2), pair{0, 2});
            run_tree_test(proofs, directed, "triangle", triangle, free(3), free(3), pair{0, 2});
            run_tree_test(proofs, directed, "square", square, free(4), free(4), pair{0, 3});
            run_tree_test(proofs, directed, "two_pieces", two_pieces, free(4), free(2), pair{0, 3});
            run_tree_test(proofs, directed, "lollipop", lollipop, free(4), free(4), pair{0, 3});

            // Anti-parallel edges, which is where the directed in-degree rule and
            // the undirected count say different things: 0 -> 1 and 1 -> 0 cannot
            // both be selected either way, but only dtree rules it out per node.
            run_tree_test(proofs, directed, "antiparallel", antiparallel, free(3), free(3), pair{0, 2});

            // A fixed root, which is how dtree is usually called.
            run_tree_test(proofs, directed, "lollipop_root0", lollipop, free(4), free(4), 0);

            // Pinned nodes and edges, so the counting rules have something to say
            // before search decides everything.
            run_tree_test(proofs, directed, "lollipop_pinned", lollipop, Ranges{1, pair{0, 1}, pair{0, 1}, 1}, free(4), pair{0, 3});
            run_tree_test(proofs, directed, "square_edges", square, free(4), Ranges{1, pair{0, 1}, pair{0, 1}, 0}, pair{0, 3});

            // A root declared wider than the node numbering.
            run_tree_test(proofs, directed, "path3_wide_root", path3, free(3), free(2), pair{-1, 4});
        }
    }

    return EXIT_SUCCESS;
}
