#include <gcs/constraints/difference/difference_simplify.hh>
#include <gcs/exception.hh>

#include <algorithm>
#include <optional>
#include <queue>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::greater;
using std::min;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::priority_queue;
using std::size_t;
using std::vector;
using std::ranges::reverse;

namespace
{
    // Strongly connected components of the zero-reduced-weight subgraph, which
    // is exactly the set of edges lying on a zero-weight cycle: reduced weights
    // are non-negative and a cycle's reduced weight equals its real weight, so a
    // cycle weighs zero iff every edge on it has reduced weight zero. Any SCC of
    // more than one node is therefore a set of variables the system forces into
    // fixed relative positions.
    //
    // Iterative Tarjan, because a scheduling network can be deep enough that a
    // recursive one would not be safe.
    auto count_zero_weight_cycles(size_t n, const vector<vector<size_t>> & zero_out, size_t & cycles, size_t & nodes_on_cycles) -> void
    {
        vector<size_t> index(n, 0), low(n, 0);
        vector<bool> on_stack(n, false);
        vector<size_t> component_stack;
        vector<pair<size_t, size_t>> work;
        size_t next_index = 1;

        for (size_t root = 0; root < n; ++root) {
            if (index[root])
                continue;
            work.emplace_back(root, 0);
            while (! work.empty()) {
                auto v = work.back().first;
                if (0 == work.back().second && 0 == index[v]) {
                    index[v] = low[v] = next_index++;
                    component_stack.push_back(v);
                    on_stack[v] = true;
                }

                if (work.back().second < zero_out[v].size()) {
                    auto w = zero_out[v][work.back().second++];
                    if (0 == index[w])
                        work.emplace_back(w, 0);
                    else if (on_stack[w])
                        low[v] = min(low[v], index[w]);
                }
                else {
                    if (low[v] == index[v]) {
                        size_t size = 0;
                        while (true) {
                            auto w = component_stack.back();
                            component_stack.pop_back();
                            on_stack[w] = false;
                            ++size;
                            if (w == v)
                                break;
                        }
                        if (size > 1) {
                            ++cycles;
                            nodes_on_cycles += size;
                        }
                    }

                    auto low_v = low[v];
                    work.pop_back();
                    if (! work.empty())
                        low[work.back().first] = min(low[work.back().first], low_v);
                }
            }
        }
    }
}

auto gcs::innards::simplify_difference_graph(size_t n, const vector<DifferenceSimplifyEdge> & edges, const vector<DifferenceSimplifyRole> & roles)
    -> DifferenceSimplifyOutcome
{
    using enum DifferenceSimplifyRole;

    if (roles.size() != edges.size())
        throw UnexpectedException{"difference logic simplification was handed a role list of the wrong length"};

    DifferenceSimplifyOutcome outcome;
    outcome.remove.resize(edges.size(), false);
    if (0 == n || edges.empty())
        return outcome;

    vector<size_t> base;
    for (size_t e = 0; e < edges.size(); ++e)
        if (Base == roles[e])
            base.push_back(e);

    // The paper's step 1: Bellman-Ford from an imaginary source v0 with a
    // zero-weight edge to every node. Seeding every potential at zero *is* that
    // source's edge set, exactly as the propagator's own passes seed from the
    // current bounds. It both detects root infeasibility and leaves
    // h(v) = wSP(v0, v), which is a valid potential function.
    vector<Integer> h(n, 0_i);
    for (size_t round = 0; round <= n; ++round) {
        bool changed = false;
        for (auto e : base) {
            auto candidate = h[edges[e].from] + edges[e].d;
            if (candidate < h[edges[e].to]) {
                h[edges[e].to] = candidate;
                changed = true;
            }
        }
        if (! changed)
            break;
        if (round == n) {
            // A shortest path from v0 is simple and so uses at most n - 1 real
            // edges, so rounds 0 .. n - 1 suffice; a relaxation in round n is
            // sound evidence of a negative cycle. Stop: the caller's own pass
            // finds and refutes it, with the cycle extraction and the
            // telescoping pol this function deliberately does not carry.
            outcome.base_negative_cycle = true;
            return outcome;
        }
    }

    // Reduced weights are non-negative for every base edge, which is what lets
    // Dijkstra run below, and a cycle's reduced weight is its real weight, since
    // every potential appears once positively and once negatively.
    vector<vector<size_t>> out(n), edges_from(n), candidates_to(n);
    vector<Integer> reduced(edges.size(), 0_i);
    for (auto e : base) {
        reduced[e] = edges[e].d + h[edges[e].from] - h[edges[e].to];
        if (reduced[e] < 0_i)
            throw UnexpectedException{"difference logic simplification computed a negative reduced weight, so its potential function is invalid"};
        out[edges[e].from].push_back(e);
    }

    vector<bool> need_source(n, false);
    for (size_t e = 0; e < edges.size(); ++e) {
        if (Ignored == roles[e])
            continue;
        // The tail, to decide whether this edge is redundant (is there a
        // strictly shorter path from `from` to `to`?).
        edges_from[edges[e].from].push_back(e);
        need_source[edges[e].from] = true;
        if (Candidate == roles[e]) {
            // And the head, to decide whether activating it would close a
            // negative cycle (how short is the path back from `to` to `from`?).
            candidates_to[edges[e].to].push_back(e);
            need_source[edges[e].to] = true;
        }
    }

    {
        vector<vector<size_t>> zero_out(n);
        for (auto e : base)
            if (0_i == reduced[e])
                zero_out[edges[e].from].push_back(edges[e].to);
        count_zero_weight_cycles(n, zero_out, outcome.zero_weight_cycles, outcome.nodes_on_zero_weight_cycles);
    }

    vector<optional<Integer>> dist(n, nullopt);
    vector<optional<size_t>> parent(n, nullopt);
    vector<size_t> touched;
    priority_queue<pair<Integer, size_t>, vector<pair<Integer, size_t>>, greater<pair<Integer, size_t>>> queue;

    // Whether some edge from u to v with weight exactly D_uv has already been
    // kept. Cleared per source, and only ever read for the source's own edges.
    vector<bool> tight_kept(n, false);

    for (size_t s = 0; s < n; ++s) {
        if (! need_source[s])
            continue;

        for (auto v : touched) {
            dist[v] = nullopt;
            parent[v] = nullopt;
            tight_kept[v] = false;
        }
        touched.clear();

        dist[s] = 0_i;
        touched.push_back(s);
        queue.emplace(0_i, s);
        while (! queue.empty()) {
            auto [reduced_distance, v] = queue.top();
            queue.pop();
            if (dist[v] != reduced_distance)
                continue;
            for (auto e : out[v]) {
                auto w = edges[e].to;
                auto candidate = reduced_distance + reduced[e];
                if (! dist[w] || candidate < *dist[w]) {
                    if (! dist[w])
                        touched.push_back(w);
                    dist[w] = candidate;
                    parent[w] = e;
                    queue.emplace(candidate, w);
                }
            }
        }

        // Undo Johnson's reweighting: a path from s to v has reduced weight
        // dist(v) = weight + h(s) - h(v).
        auto real_distance = [&](size_t v) { return *dist[v] - h[s] + h[v]; };

        // Redundant edges, both kinds. An active edge goes when a strictly
        // shorter path already implies it; among edges that *attain* the
        // distance, exactly one is kept, since dropping them all would change
        // the distance. An implied edge goes on the weaker test, because one
        // that merely restates a distance the base graph already has can never
        // add anything even when its condition becomes true.
        for (auto e : edges_from[s]) {
            auto v = edges[e].to;
            if (! dist[v])
                continue;
            auto distance = real_distance(v);
            if (Candidate == roles[e]) {
                if (edges[e].d >= distance)
                    outcome.remove[e] = true;
            }
            else if (edges[e].d > distance)
                outcome.remove[e] = true;
            else if (edges[e].d == distance) {
                if (tight_kept[v])
                    outcome.remove[e] = true;
                else
                    tight_kept[v] = true;
            }
        }

        // Conditions that must be false: the candidate edge u --d--> v plus the
        // shortest path v ~> u is a cycle, and if it weighs less than zero then
        // the condition holding would make the system infeasible. This is the
        // paper's step 3, and it is the only conclusion here that needs a proof.
        for (auto e : candidates_to[s]) {
            if (outcome.remove[e])
                continue;
            auto u = edges[e].from;
            if (! dist[u])
                continue;
            if (edges[e].d + real_distance(u) >= 0_i)
                continue;

            vector<size_t> path;
            auto at = u;
            while (at != s) {
                if (! parent[at])
                    throw UnexpectedException{"difference logic simplification lost the witness path for a condition it wants to fix"};
                path.push_back(*parent[at]);
                at = edges[*parent[at]].from;
            }
            reverse(path);
            outcome.fix.emplace_back(e, move(path));
        }
    }

    return outcome;
}
