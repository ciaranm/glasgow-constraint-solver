#include <gcs/constraints/difference/difference_incremental.hh>
#include <gcs/exception.hh>

#include <algorithm>
#include <cstddef>
#include <functional>
#include <optional>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::greater;
using std::nullopt;
using std::optional;
using std::pair;
using std::size_t;
using std::vector;
using std::ranges::make_heap;
using std::ranges::pop_heap;
using std::ranges::push_heap;

auto gcs::innards::build_difference_adjacency(size_t number_of_nodes, const vector<DifferenceArc> & arcs, bool by_tail) -> DifferenceAdjacency
{
    DifferenceAdjacency result;
    result.start.assign(number_of_nodes + 1, 0);
    result.arcs.resize(arcs.size());

    auto end_of = [&](const DifferenceArc & a) { return by_tail ? a.from : a.to; };

    for (const auto & a : arcs)
        ++result.start[end_of(a) + 1];
    for (size_t v = 0; v < number_of_nodes; ++v)
        result.start[v + 1] += result.start[v];

    auto next = result.start;
    for (size_t e = 0; e < arcs.size(); ++e)
        result.arcs[next[end_of(arcs[e])]++] = e;

    return result;
}

auto gcs::innards::difference_initial_potential(size_t number_of_nodes, const vector<DifferenceArc> & arcs, const vector<char> & active)
    -> optional<vector<Integer>>
{
    // Bellman-Ford from an imaginary source with a zero-weight edge to every
    // node: seeding every potential at zero *is* that source's edge set, exactly
    // as the propagator's own passes encode the bounds. What comes out is
    // pi(v) = wSP(source, v), so pi(v) <= pi(u) + d for every arc u --d--> v,
    // which is the potential invariant.
    //
    // A shortest path out of the source is simple, so after the seeding it uses
    // at most n - 1 real arcs and n - 1 rounds suffice; one more that still
    // relaxes something is sound evidence of a negative cycle.
    vector<Integer> potential(number_of_nodes, 0_i);

    for (size_t round = 0; round <= number_of_nodes; ++round) {
        bool changed = false;
        for (size_t e = 0; e < arcs.size(); ++e) {
            if (! difference_arc_is_active(active, e))
                continue;
            auto candidate = potential[arcs[e].from] + arcs[e].d;
            if (candidate < potential[arcs[e].to]) {
                potential[arcs[e].to] = candidate;
                changed = true;
            }
        }
        if (! changed)
            return potential;
    }

    return nullopt;
}

auto gcs::innards::difference_invalid_potential_arc(
    const vector<DifferenceArc> & arcs, const vector<char> & active, const vector<Integer> & potential) -> optional<size_t>
{
    for (size_t e = 0; e < arcs.size(); ++e)
        if (difference_arc_is_active(active, e) && potential[arcs[e].from] + arcs[e].d - potential[arcs[e].to] < 0_i)
            return e;
    return nullopt;
}

auto gcs::innards::difference_repair_potential(size_t number_of_nodes, const vector<DifferenceArc> & arcs, const DifferenceAdjacency & by_tail,
    const vector<char> & active, vector<Integer> & potential, size_t added_arc, DifferencePotentialWorkspace & work) -> bool
{
    // The paper's Algorithm 1 (Cotton and Maler's IncSat). gamma is zero
    // everywhere except at the nodes this call touches, and is restored to that
    // on the way out, so a wake that adds no arc pays nothing and a wake that
    // does pays only for what it reached.
    if (work.gamma.size() != number_of_nodes) {
        work.gamma.assign(number_of_nodes, 0_i);
        work.updated.assign(number_of_nodes, 0_i);
        work.is_updated.assign(number_of_nodes, 0);
    }
    work.touched.clear();
    work.heap.clear();

    auto source = arcs[added_arc].from, target = arcs[added_arc].to;
    auto result = true;

    // gamma(target) := pi(source) + d - pi(target), the reduced cost of the new
    // arc. Non-negative means the potential is already valid for it and there is
    // nothing at all to do, which is the common case.
    auto initial = potential[source] + arcs[added_arc].d - potential[target];
    if (initial < 0_i) {
        work.gamma[target] = initial;
        work.touched.push_back(target);
        work.heap.emplace_back(initial, target);
        make_heap(work.heap, greater{});

        while (! work.heap.empty()) {
            // The loop's other termination condition: once the repair has
            // reached back round to the new arc's own tail, the arc lies on a
            // negative cycle and no potential function exists.
            if (work.gamma[source] < 0_i) {
                result = false;
                break;
            }

            pop_heap(work.heap, greater{});
            auto [gamma_here, here] = work.heap.back();
            work.heap.pop_back();
            if (gamma_here != work.gamma[here])
                continue;

            work.updated[here] = potential[here] + gamma_here;
            work.is_updated[here] = 1;
            work.gamma[here] = 0_i;

            for (auto i = by_tail.start[here]; i != by_tail.start[here + 1]; ++i) {
                auto e = by_tail.arcs[i];
                if (! difference_arc_is_active(active, e))
                    continue;
                auto next = arcs[e].to;
                // The paper's line 9, `if pi'(t) = pi(t)': a node whose
                // potential has already been lowered is never revisited, which
                // is what bounds the loop at one update per node.
                if (work.is_updated[next])
                    continue;
                auto candidate = work.updated[here] + arcs[e].d - potential[next];
                if (candidate < work.gamma[next]) {
                    if (0_i == work.gamma[next])
                        work.touched.push_back(next);
                    work.gamma[next] = candidate;
                    work.heap.emplace_back(candidate, next);
                    push_heap(work.heap, greater{});
                }
            }
        }

        if (result && work.gamma[source] < 0_i)
            result = false;

        // Commit only on success: an unsatisfiable addition must leave the
        // potential exactly as it was, because the caller may go on to refute
        // using the from-scratch pass and the arc may be back tomorrow.
        if (result)
            for (auto v : work.touched)
                if (work.is_updated[v])
                    potential[v] = work.updated[v];
    }

    for (auto v : work.touched) {
        work.gamma[v] = 0_i;
        work.is_updated[v] = 0;
    }

    return result;
}

auto gcs::innards::difference_incremental_bounds(size_t number_of_nodes, const vector<DifferenceArc> & arcs, const DifferenceAdjacency & adjacency,
    bool by_tail, const vector<char> & active, const vector<Integer> & potential, const vector<Integer> & bound, const vector<Integer> & gate,
    const vector<char> & forced, DifferenceBoundsWorkspace & work) -> void
{
    work.settle_order.clear();
    if (work.gamma.size() != number_of_nodes) {
        work.gamma.assign(number_of_nodes, 0_i);
        work.queued.assign(number_of_nodes, 0);
        work.settled.assign(number_of_nodes, 0);
        work.has_predecessor.assign(number_of_nodes, 0);
        work.predecessor.assign(number_of_nodes, 0);
        work.settled_bound.assign(number_of_nodes, 0_i);
    }
    work.heap.clear();

    // Vl: the nodes whose bound has moved since the last run, plus the nodes an
    // arc activation has forced in. The paper's Algorithm 3 line 1 and the
    // section 4.4 recipe its section 5.4 leaves out, in one place.
    auto in_start_set = [&](size_t v) { return bound[v] > gate[v] || 0 != forced[v]; };

    // pi(v0) is a **per-call temporary**, computed over Vl and nothing else. It
    // is what makes every seed non-negative, so caching it across calls (where
    // Vl is different) or computing it over all of V would let a negative seed
    // into the queue and corrupt Dijkstra's settle order --- which loses
    // propagation silently, since no proof can see it. It is deliberately not
    // stored anywhere.
    bool any = false;
    Integer pi_v0{0};
    for (size_t v = 0; v < number_of_nodes; ++v)
        if (in_start_set(v)) {
            auto here = bound[v] + potential[v];
            if (! any || here > pi_v0)
                pi_v0 = here;
            any = true;
        }

    if (! any)
        return;

    for (size_t v = 0; v < number_of_nodes; ++v)
        if (in_start_set(v)) {
            // The reduced cost of the imaginary edge v0 --(-bound(v))--> v,
            // which is >= 0 exactly because pi_v0 is the maximum above.
            work.gamma[v] = pi_v0 - bound[v] - potential[v];
            work.queued[v] = 1;
            work.has_predecessor[v] = 0;
            work.heap.emplace_back(work.gamma[v], v);
        }
    make_heap(work.heap, greater{});

    while (! work.heap.empty()) {
        pop_heap(work.heap, greater{});
        auto [gamma_here, here] = work.heap.back();
        work.heap.pop_back();
        if (work.settled[here] || gamma_here != work.gamma[here])
            continue;

        work.settled[here] = 1;
        work.settle_order.push_back(here);

        // wSP(v0, here) is gamma_here in reduced costs, so the real weight is
        // gamma_here + pi(here) - pi(v0) and the bound it licenses is its
        // negation. (The paper's line 11, read as "distance *from* v0" --- its
        // delta arrow notation is not self-consistent with its section 3.1.)
        work.settled_bound[here] = pi_v0 - gamma_here - potential[here];

        // Algorithm 3 line 12, the expansion gate, and the whole point of the
        // Do array. If this node's new bound does not beat the bound the last
        // run propagated from, then invariant I2 says every node downstream of
        // it already knows everything this route could tell it, so the entire
        // sub-search is dead. A forced node is expanded regardless: its arc was
        // not in the graph last time, so I2 says nothing about it.
        if (! (work.settled_bound[here] > gate[here] || 0 != forced[here]))
            continue;

        for (auto i = adjacency.start[here]; i != adjacency.start[here + 1]; ++i) {
            auto e = adjacency.arcs[i];
            if (! difference_arc_is_active(active, e))
                continue;
            auto next = by_tail ? arcs[e].to : arcs[e].from;
            // Algorithm 3 line 14: a settled node has its final distance, and
            // in the reduced-cost graph no later relaxation can improve it.
            if (work.settled[next])
                continue;

            // Note gamma_here, not gamma[here]: the pseudocode's lines 15-16
            // read gamma(s) after line 10 has set it to +infinity, which makes
            // the test always false and the algorithm never propagate anything.
            // The value intended is wSP(v0, s), saved before the reset.
            auto reduced = potential[here] + arcs[e].d - potential[next];
            if (reduced < 0_i)
                throw UnexpectedException{"difference logic found a negative reduced cost, so its potential function is invalid"};
            auto candidate = gamma_here + reduced;

            if (! work.queued[next] || candidate < work.gamma[next]) {
                work.gamma[next] = candidate;
                work.queued[next] = 1;
                work.has_predecessor[next] = 1;
                work.predecessor[next] = e;
                work.heap.emplace_back(candidate, next);
                push_heap(work.heap, greater{});
            }
        }
    }

    // Every queued node ends up settled, because the loop drains the heap, so
    // the settle order is enough to reset the flags for the next call.
    for (auto v : work.settle_order) {
        work.queued[v] = 0;
        work.settled[v] = 0;
    }
}
