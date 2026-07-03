#include <gcs/constraints/global_cardinality/gac_global_cardinality.hh>
#include <gcs/constraints/global_cardinality/hints.hh>
#include <gcs/constraints/global_cardinality/justify.hh>
#include <gcs/constraints/in.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <algorithm>
#include <cstdint>
#include <functional>
#include <limits>
#include <set>
#include <sstream>
#include <string>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::fill;
using std::function;
using std::make_unique;
using std::min;
using std::move;
using std::nullopt;
using std::numeric_limits;
using std::optional;
using std::pair;
using std::set;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

namespace
{
    // A small max-flow (Dinic) used to find a feasible flow with lower bounds.
    struct MaxFlow
    {
        struct Edge
        {
            int to;
            long long cap;
            int rev;
        };

        vector<vector<Edge>> g;
        vector<int> level, iter;

        explicit MaxFlow(int n) : g(n), level(n), iter(n)
        {
        }

        // Returns the index of the forward edge within g[u].
        auto add_edge(int u, int v, long long cap) -> pair<int, int>
        {
            auto fwd = pair<int, int>{u, static_cast<int>(g[u].size())};
            g[u].push_back(Edge{v, cap, static_cast<int>(g[v].size())});
            g[v].push_back(Edge{u, 0, static_cast<int>(g[u].size()) - 1});
            return fwd;
        }

        auto bfs(int s, int t) -> bool
        {
            fill(level.begin(), level.end(), -1);
            vector<int> q;
            q.push_back(s);
            level[s] = 0;
            for (std::size_t h = 0; h < q.size(); ++h) {
                auto u = q[h];
                for (auto & e : g[u])
                    if (e.cap > 0 && level[e.to] < 0) {
                        level[e.to] = level[u] + 1;
                        q.push_back(e.to);
                    }
            }
            return level[t] >= 0;
        }

        auto dfs(int u, int t, long long f) -> long long
        {
            if (u == t)
                return f;
            for (auto & i = iter[u]; i < static_cast<int>(g[u].size()); ++i) {
                auto & e = g[u][i];
                if (e.cap > 0 && level[u] < level[e.to]) {
                    auto d = dfs(e.to, t, min(f, e.cap));
                    if (d > 0) {
                        e.cap -= d;
                        g[e.to][e.rev].cap += d;
                        return d;
                    }
                }
            }
            return 0;
        }

        auto max_flow(int s, int t) -> long long
        {
            long long flow = 0;
            while (bfs(s, t)) {
                fill(iter.begin(), iter.end(), 0);
                while (auto f = dfs(s, t, numeric_limits<long long>::max()))
                    flow += f;
            }
            return flow;
        }

        // The flow currently pushed along the forward edge g[u][k] equals the
        // capacity that has accumulated on its reverse edge.
        auto flow_on(int u, int k) const -> long long
        {
            const auto & e = g[u][k];
            return g[e.to][e.rev].cap;
        }
    };
}

auto gcs::innards::propagate_gac_global_cardinality(const vector<IntegerVariableID> & vars, const ConstraintID & owner,
    const vector<Integer> & values, const vector<IntegerVariableID> & counts, bool closed,
    const vector<pair<optional<ProofLine>, optional<ProofLine>>> & count_lines, const vector<IntegerVariableID> & all_vars, const State & state,
    auto & inference, ProofLogger * const logger) -> PropagatorState
{
    auto m = values.size();
    auto n = vars.size();

    // Per-value count bounds: keep the count variables pinned to the
    // must-occur..can-occur range (so they are determined at a leaf).
    // These are the certified per-value RUP steps from the BC propagator.
    for (const auto & [j, value] : enumerate(values)) {
        ReasonLiterals fixed_eq, absent_ne;
        Integer must = 0_i, can = 0_i;
        for (const auto & var : vars) {
            if (state.in_domain(var, value)) {
                ++can;
                if (state.has_single_value(var)) {
                    ++must;
                    fixed_eq.emplace_back(var == value);
                }
            }
            else
                absent_ne.emplace_back(var != value);
        }
        auto [lb_j, ub_j] = state.bounds(counts[j]);
        if (must > lb_j)
            inference.infer(logger, counts[j] >= must, JustifyUsingRUP{hints::GlobalCardinality{owner}}, ExplicitReason{fixed_eq});
        if (can < ub_j)
            inference.infer(logger, counts[j] <= can, JustifyUsingRUP{hints::GlobalCardinality{owner}}, ExplicitReason{absent_ne});
    }

    // Build Régin's value graph as a flow network and find a feasible
    // flow with lower bounds. Every variable must be assigned (var->T is
    // [1,1]); in the open case a dummy value of capacity [0,n] absorbs
    // the variables that take a non-cover value. Node layout: 0 = source,
    // 1 = sink, 2+j = value j, 2+m = dummy value, 2+m+1+i = variable i,
    // then a super source/sink for the lower-bound reduction.
    auto S = 0, T = 1;
    auto value_node = [&](std::size_t j) { return 2 + static_cast<int>(j); };
    auto dummy_node = 2 + static_cast<int>(m);
    auto var_node = [&](std::size_t i) { return 2 + static_cast<int>(m) + 1 + static_cast<int>(i); };
    auto base_nodes = 2 + static_cast<int>(m) + 1 + static_cast<int>(n);
    auto SS = base_nodes, TT = base_nodes + 1;
    MaxFlow mf(base_nodes + 2);

    set<Integer> cover(values.begin(), values.end());
    long long inf = static_cast<long long>(n) + 1;

    // Original edges with lower bounds, recorded so we can recover the
    // feasible flow and build the residual.
    struct OrigEdge
    {
        int from, to;
        long long lo, hi;
        int u, k; // location of the reduced (hi - lo) edge in mf.g
    };
    vector<OrigEdge> orig;
    vector<long long> excess(base_nodes + 2, 0);

    auto add_orig = [&](int u, int v, long long lo, long long hi) {
        auto [a, k] = mf.add_edge(u, v, hi - lo);
        orig.push_back(OrigEdge{u, v, lo, hi, a, k});
        excess[v] += lo;
        excess[u] -= lo;
    };

    // value->var assignment edges; remember which OrigEdge each is.
    vector<vector<int>> assign_edge(m, vector<int>(n, -1));
    for (const auto & [j, value] : enumerate(values)) {
        auto [c_lo, c_hi] = state.bounds(counts[j]);
        if (c_lo < 0_i)
            c_lo = 0_i;
        add_orig(S, value_node(j), c_lo.raw_value, c_hi.raw_value);
        for (std::size_t i = 0; i < n; ++i)
            if (state.in_domain(vars[i], value)) {
                assign_edge[j][i] = static_cast<int>(orig.size());
                add_orig(value_node(j), var_node(i), 0, 1);
            }
    }
    vector<int> dummy_edge(n, -1);
    if (! closed) {
        add_orig(S, dummy_node, 0, inf);
        for (std::size_t i = 0; i < n; ++i) {
            bool has_non_cover = false;
            for (const auto & val : state.each_value_immutable(vars[i]))
                if (! cover.contains(val)) {
                    has_non_cover = true;
                    break;
                }
            if (has_non_cover) {
                dummy_edge[i] = static_cast<int>(orig.size());
                add_orig(dummy_node, var_node(i), 0, 1);
            }
        }
    }
    for (std::size_t i = 0; i < n; ++i)
        add_orig(var_node(i), T, 1, 1);
    add_orig(T, S, 0, inf);

    // Lower-bound reduction: balance the excess through SS/TT.
    long long need = 0;
    for (int node = 0; node < base_nodes; ++node) {
        if (excess[node] > 0) {
            mf.add_edge(SS, node, excess[node]);
            need += excess[node];
        }
        else if (excess[node] < 0)
            mf.add_edge(node, TT, -excess[node]);
    }

    auto feasible = (mf.max_flow(SS, TT) == need);

    // Flow on each original edge (the partial flow when infeasible).
    vector<long long> flow(orig.size());
    for (const auto & [idx, e] : enumerate(orig))
        flow[idx] = e.lo + mf.flow_on(e.u, e.k);

    if (! feasible) {
        // A variable the flow could not assign (no incoming assignment)
        // witnesses a capacity-driven Hall violator: grow a set of
        // variables confined to cover values whose total upper capacity
        // is too small. (Demand-driven infeasibility -- too much lower
        // demand for the suppliers -- is still asserted.)
        int unmatched = -1;
        for (std::size_t i = 0; i < n && unmatched < 0; ++i) {
            long long in = 0;
            for (std::size_t j = 0; j < m; ++j)
                if (assign_edge[j][i] >= 0)
                    in += flow[assign_edge[j][i]];
            if (dummy_edge[i] >= 0)
                in += flow[dummy_edge[i]];
            if (in == 0)
                unmatched = static_cast<int>(i);
        }

        vector<std::size_t> cut_values;
        vector<IntegerVariableID> confined;
        if (unmatched >= 0) {
            vector<std::uint8_t> hv_var(n, 0), hv_val(m, 0);
            hv_var[unmatched] = 1;
            bool grew = true;
            while (grew) {
                grew = false;
                for (std::size_t j = 0; j < m; ++j) {
                    if (hv_val[j])
                        continue;
                    bool in_neighbourhood = false;
                    for (std::size_t i = 0; i < n; ++i)
                        if (hv_var[i] && state.in_domain(vars[i], values[j])) {
                            in_neighbourhood = true;
                            break;
                        }
                    if (! in_neighbourhood)
                        continue;
                    hv_val[j] = 1;
                    grew = true;
                    for (std::size_t i = 0; i < n; ++i)
                        if (assign_edge[j][i] >= 0 && flow[assign_edge[j][i]] == 1)
                            hv_var[i] = 1;
                }
            }
            for (std::size_t j = 0; j < m; ++j)
                if (hv_val[j])
                    cut_values.push_back(j);
            // Confine to the variables that can only take cut values.
            set<Integer> hall;
            for (auto j : cut_values)
                hall.insert(values[j]);
            Integer cap = 0_i;
            for (auto j : cut_values)
                cap += state.bounds(counts[j]).second;
            for (std::size_t i = 0; i < n; ++i) {
                bool subset = true;
                for (const auto & val : state.each_value_immutable(vars[i]))
                    if (! hall.contains(val)) {
                        subset = false;
                        break;
                    }
                if (subset)
                    confined.push_back(vars[i]);
            }
            if (Integer(confined.size()) <= cap) {
                cut_values.clear();
                confined.clear();
            }
        }

        // Demand-driven Hall violator (dual of the capacity one): grow
        // from an under-supplied value a set of cover values whose total
        // lower demand exceeds the variables that can supply them.
        vector<std::size_t> demand_cut;
        vector<IntegerVariableID> suppliers;
        if (cut_values.empty()) {
            int under = -1;
            for (std::size_t j = 0; j < m && under < 0; ++j) {
                long long assigned = 0;
                for (std::size_t i = 0; i < n; ++i)
                    if (assign_edge[j][i] >= 0)
                        assigned += flow[assign_edge[j][i]];
                if (assigned < state.bounds(counts[j]).first.raw_value)
                    under = static_cast<int>(j);
            }
            if (under >= 0) {
                vector<std::uint8_t> hv_val(m, 0), hv_var(n, 0);
                hv_val[under] = 1;
                bool grew = true;
                while (grew) {
                    grew = false;
                    for (std::size_t i = 0; i < n; ++i) {
                        if (hv_var[i])
                            continue;
                        bool meets = false;
                        for (std::size_t j = 0; j < m; ++j)
                            if (hv_val[j] && state.in_domain(vars[i], values[j])) {
                                meets = true;
                                break;
                            }
                        if (! meets)
                            continue;
                        hv_var[i] = 1;
                        grew = true;
                        for (std::size_t j = 0; j < m; ++j)
                            if (! hv_val[j] && assign_edge[j][i] >= 0 && flow[assign_edge[j][i]] == 1)
                                hv_val[j] = 1;
                    }
                }
                Integer demand = 0_i;
                for (std::size_t j = 0; j < m; ++j)
                    if (hv_val[j]) {
                        demand_cut.push_back(j);
                        demand += state.bounds(counts[j]).first;
                    }
                for (std::size_t i = 0; i < n; ++i)
                    if (hv_var[i])
                        suppliers.push_back(vars[i]);
                if (Integer(suppliers.size()) >= demand) {
                    demand_cut.clear();
                    suppliers.clear();
                }
            }
        }

        if (! cut_values.empty())
            inference.contradiction(logger,
                JustifyExplicitly{[&, cut_values, confined](const ReasonLiterals &) {
                                      emit_gcc_capacity_pol(*logger, state, vars, values, counts, count_lines, cut_values, confined);
                                  },
                    ThenRUP::Yes, hints::GlobalCardinality{owner}},
                LazyReasonOver{vars, [&, cut_values, confined](const State &, ReasonLiterals & out) {
                                   out = gcc_capacity_reason(state, values, counts, cut_values, confined);
                               }});
        else if (! demand_cut.empty())
            inference.contradiction(logger,
                JustifyExplicitly{//
                    [&, demand_cut, suppliers](const ReasonLiterals &) {
                        emit_gcc_demand_pol(*logger, state, vars, values, counts, count_lines, demand_cut, suppliers, nullopt, nullopt);
                    },
                    ThenRUP::Yes, hints::GlobalCardinality{owner}},
                LazyReasonOver{vars, [&, demand_cut, suppliers](const State &, ReasonLiterals & out) {
                                   out = gcc_demand_reason(state, vars, values, counts, demand_cut, suppliers);
                               }});
        else if (closed && unmatched >= 0)
            // A closed variable with no cover value left: the per-variable
            // In constraint certifies this, so leave it to that rather
            // than raise an unjustified contradiction here.
            return PropagatorState::Enable;
        else
            // An infeasible flow has either an unassignable variable
            // (capacity Hall violator) or an under-supplied value (demand
            // Hall violator), so one of the branches above should have
            // fired. Reaching here means the violator search missed it:
            // fail loudly rather than emit an unjustified contradiction.
            throw UnexpectedException{"global cardinality: infeasible flow with no Hall violator found"};
        return PropagatorState::Enable;
    }

    vector<vector<int>> radj(base_nodes);
    for (const auto & [idx, e] : enumerate(orig)) {
        if (flow[idx] < e.hi)
            radj[e.from].push_back(e.to);
        if (flow[idx] > e.lo)
            radj[e.to].push_back(e.from);
    }

    // Tarjan strongly-connected components of the residual.
    vector<int> index(base_nodes, 0), low(base_nodes, 0), comp(base_nodes, -1);
    vector<std::uint8_t> on_stack(base_nodes, 0);
    vector<int> stk;
    int next_index = 1, n_comp = 0;
    function<void(int)> scc = [&](int v) {
        index[v] = low[v] = next_index++;
        stk.push_back(v);
        on_stack[v] = 1;
        for (auto w : radj[v]) {
            if (index[w] == 0) {
                scc(w);
                low[v] = min(low[v], low[w]);
            }
            else if (on_stack[w])
                low[v] = min(low[v], index[w]);
        }
        if (low[v] == index[v]) {
            int w;
            do {
                w = stk.back();
                stk.pop_back();
                on_stack[w] = 0;
                comp[w] = n_comp;
            } while (w != v);
            ++n_comp;
        }
    };
    for (int v = 0; v < base_nodes; ++v)
        if (index[v] == 0)
            scc(v);

    // Residual reachability from a node (for extracting the proof cut).
    auto reachable_from = [&](int start) {
        vector<std::uint8_t> seen(base_nodes, 0);
        vector<int> q{start};
        seen[start] = 1;
        for (std::size_t h = 0; h < q.size(); ++h)
            for (auto w : radj[q[h]])
                if (! seen[w]) {
                    seen[w] = 1;
                    q.push_back(w);
                }
        return seen;
    };

    auto value_index = [&](Integer val) -> int {
        for (std::size_t v = 0; v < m; ++v)
            if (values[v] == val)
                return static_cast<int>(v);
        return -1;
    };

    // An assignment edge value j -> var i that carries no flow and
    // crosses two components has no support: prune it, justified by the
    // cut reachable from the variable. If the source is in that cut the
    // pruning is capacity-driven (the values *outside* the cut are full);
    // otherwise it is demand-driven (the values *inside* the cut are at
    // their lower bound).
    for (const auto & [j, value] : enumerate(values))
        for (std::size_t i = 0; i < n; ++i) {
            auto ei = assign_edge[j][i];
            if (ei < 0)
                continue;
            if (! (flow[ei] == 0 && comp[value_node(j)] != comp[var_node(i)]))
                continue;

            auto seen = reachable_from(var_node(i));
            if (seen[S]) {
                // Capacity cut: full cover values are those not reachable.
                vector<std::size_t> cut_values;
                for (std::size_t v = 0; v < m; ++v)
                    if (! seen[value_node(v)])
                        cut_values.push_back(v);
                vector<IntegerVariableID> confined;
                for (std::size_t k = 0; k < n; ++k) {
                    bool subset = true;
                    for (const auto & val : state.each_value_immutable(vars[k])) {
                        auto vi = value_index(val);
                        if (vi < 0 || seen[value_node(static_cast<std::size_t>(vi))]) {
                            subset = false;
                            break;
                        }
                    }
                    if (subset)
                        confined.push_back(vars[k]);
                }
                inference.infer(logger, vars[i] != value,
                    JustifyExplicitly{[&, cut_values, confined](const ReasonLiterals &) {
                                          emit_gcc_capacity_pol(*logger, state, vars, values, counts, count_lines, cut_values, confined);
                                      },
                        ThenRUP::Yes, hints::GlobalCardinality{owner}},
                    LazyReasonOver{vars, [&, cut_values, confined](const State &, ReasonLiterals & out) {
                                       out = gcc_capacity_reason(state, values, counts, cut_values, confined);
                                   }});
            }
            else {
                // Demand cut: cover values inside the cut are at their lower bound.
                vector<std::size_t> cut_values;
                for (std::size_t v = 0; v < m; ++v)
                    if (seen[value_node(v)])
                        cut_values.push_back(v);
                // The at-most-ones must cover every variable that can take
                // a cut value, matching the reason's exclusions.
                vector<IntegerVariableID> potential;
                for (std::size_t k = 0; k < n; ++k) {
                    bool meets = false;
                    for (auto v : cut_values)
                        if (state.in_domain(vars[k], values[v])) {
                            meets = true;
                            break;
                        }
                    if (meets)
                        potential.push_back(vars[k]);
                }
                inference.infer(logger, vars[i] != value,
                    JustifyExplicitly{//
                        [&, cut_values, potential, value = value, i = i](const ReasonLiterals &) {
                            emit_gcc_demand_pol(*logger, state, vars, values, counts, count_lines, cut_values, potential, vars[i], value);
                        },
                        ThenRUP::Yes, hints::GlobalCardinality{owner}},
                    LazyReasonOver{vars, [&, cut_values, potential](const State &, ReasonLiterals & out) {
                                       out = gcc_demand_reason(state, vars, values, counts, cut_values, potential);
                                   }});
            }
        }

    // Likewise the dummy edge: if a variable cannot route through the
    // dummy value, it cannot take any non-cover value. This is always a
    // demand cut (the cover values' lower bounds force the variable in),
    // so the source is not in the cut reachable from it.
    for (std::size_t i = 0; i < n; ++i) {
        auto ei = dummy_edge[i];
        if (! (ei >= 0 && flow[ei] == 0 && comp[dummy_node] != comp[var_node(i)]))
            continue;
        auto seen = reachable_from(var_node(i));
        vector<std::size_t> cut_values;
        for (std::size_t v = 0; v < m; ++v)
            if (seen[value_node(v)])
                cut_values.push_back(v);
        vector<IntegerVariableID> potential;
        for (std::size_t k = 0; k < n; ++k) {
            bool meets = false;
            for (auto v : cut_values)
                if (state.in_domain(vars[k], values[v])) {
                    meets = true;
                    break;
                }
            if (meets)
                potential.push_back(vars[k]);
        }
        for (const auto & val : state.each_value_mutable(vars[i]))
            if (! cover.contains(val))
                inference.infer(logger, vars[i] != val,
                    JustifyExplicitly{//
                        [&, cut_values, potential, val = val, i = i](const ReasonLiterals &) {
                            emit_gcc_demand_pol(*logger, state, vars, values, counts, count_lines, cut_values, potential, vars[i], val);
                        },
                        ThenRUP::Yes, hints::GlobalCardinality{owner}},
                    LazyReasonOver{vars, [&, cut_values, potential](const State &, ReasonLiterals & out) {
                                       out = gcc_demand_reason(state, vars, values, counts, cut_values, potential);
                                   }});
    }

    return PropagatorState::Enable;
}

template auto gcs::innards::propagate_gac_global_cardinality(const std::vector<IntegerVariableID> & vars, const ConstraintID & owner,
    const std::vector<Integer> & values, const std::vector<IntegerVariableID> & counts, bool closed,
    const std::vector<std::pair<std::optional<ProofLine>, std::optional<ProofLine>>> & count_lines, const std::vector<IntegerVariableID> & all_vars,
    const State & state, SimpleInferenceTracker & inference, ProofLogger * const logger) -> PropagatorState;

template auto gcs::innards::propagate_gac_global_cardinality(const std::vector<IntegerVariableID> & vars, const ConstraintID & owner,
    const std::vector<Integer> & values, const std::vector<IntegerVariableID> & counts, bool closed,
    const std::vector<std::pair<std::optional<ProofLine>, std::optional<ProofLine>>> & count_lines, const std::vector<IntegerVariableID> & all_vars,
    const State & state, EagerProofLoggingInferenceTracker & inference, ProofLogger * const logger) -> PropagatorState;
