#include <gcs/constraints/dag/dag.hh>
#include <gcs/constraints/dag/hints.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <algorithm>
#include <memory>
#include <string>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::innards::dag;

using std::holds_alternative;
using std::make_unique;
using std::move;
using std::pair;
using std::size_t;
using std::string;
using std::to_string;
using std::unique_ptr;
using std::vector;

namespace
{
    /// A part of the graph that could hold a cycle: a strongly connected component
    /// of the *input* graph with more than one node, or a single node with a self
    /// loop. `nodes` is sorted, and `edges` lists the input edges with both
    /// endpoints inside.
    struct CyclicPart
    {
        vector<size_t> nodes;
        vector<size_t> edges;
    };

    /// Tarjan's algorithm, iteratively so that a long chain cannot overflow the
    /// stack, keeping only the components that could hold a cycle. An edge between
    /// two components can never sit on a cycle of any selected subgraph, because a
    /// cycle is strongly connected and so lies inside one component; such an edge
    /// therefore needs no level rows at all, only the subgraph ones.
    auto cyclic_parts_of(size_t n, const vector<pair<size_t, size_t>> & edges) -> vector<CyclicPart>
    {
        vector<vector<size_t>> leaving(n);
        for (size_t e = 0; e != edges.size(); ++e)
            leaving[edges[e].first].push_back(e);

        vector<size_t> index(n, 0), low(n, 0), component(n, 0), stack, call_node, call_position;
        vector<bool> on_stack(n, false), visited(n, false);
        size_t next_index = 1, next_component = 0;

        for (size_t start = 0; start != n; ++start) {
            if (visited[start])
                continue;
            call_node.push_back(start);
            call_position.push_back(0);
            index[start] = low[start] = next_index++;
            visited[start] = true;
            stack.push_back(start);
            on_stack[start] = true;

            while (! call_node.empty()) {
                auto v = call_node.back();
                // By index rather than by reference into call_position, which the
                // push_back below can reallocate out from under one.
                auto position = call_position.size() - 1;
                if (call_position[position] != leaving[v].size()) {
                    auto w = edges[leaving[v][call_position[position]++]].second;
                    if (! visited[w]) {
                        index[w] = low[w] = next_index++;
                        visited[w] = true;
                        stack.push_back(w);
                        on_stack[w] = true;
                        call_node.push_back(w);
                        call_position.push_back(0);
                    }
                    else if (on_stack[w])
                        low[v] = std::min(low[v], index[w]);
                }
                else {
                    if (low[v] == index[v]) {
                        while (true) {
                            auto w = stack.back();
                            stack.pop_back();
                            on_stack[w] = false;
                            component[w] = next_component;
                            if (w == v)
                                break;
                        }
                        ++next_component;
                    }
                    call_node.pop_back();
                    call_position.pop_back();
                    if (! call_node.empty())
                        low[call_node.back()] = std::min(low[call_node.back()], low[v]);
                }
            }
        }

        vector<CyclicPart> parts(next_component);
        for (size_t v = 0; v != n; ++v)
            parts[component[v]].nodes.push_back(v);
        for (size_t e = 0; e != edges.size(); ++e)
            if (component[edges[e].first] == component[edges[e].second])
                parts[component[edges[e].first]].edges.push_back(e);

        // A component of one node holds a cycle only if that node has a self loop;
        // one of two or more always does, being strongly connected.
        vector<CyclicPart> cyclic;
        for (auto & part : parts)
            if (part.nodes.size() > 1 || ! part.edges.empty())
                cyclic.push_back(move(part));
        return cyclic;
    }
}

Dag::Dag(vector<pair<size_t, size_t>> edges, vector<IntegerVariableID> ns, vector<IntegerVariableID> es) :
    _edges(move(edges)), _ns(move(ns)), _es(move(es))
{
}

auto Dag::clone() const -> unique_ptr<Constraint>
{
    auto result = make_unique<Dag>(_edges, _ns, _es);
    result->_proof_mutation = _proof_mutation;
    return result;
}

auto Dag::constraint_type() const -> string
{
    return "dag";
}

auto Dag::with_proof_mutation(DagProofMutation mutation) -> Dag &
{
    _proof_mutation = mutation;
    return *this;
}

auto Dag::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    vector<SExpr> from, to, ns, es;
    for (const auto & [u, v] : _edges) {
        from.push_back(SExpr::atom(to_string(u)));
        to.push_back(SExpr::atom(to_string(v)));
    }
    for (const auto & v : _ns)
        ns.push_back(tracker.s_expr_term_of(v));
    for (const auto & v : _es)
        es.push_back(tracker.s_expr_term_of(v));
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(move(from)), SExpr::list(move(to)),
        SExpr::list(move(ns)), SExpr::list(move(es))});
}

auto Dag::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    if (_edges.size() != _es.size())
        throw InvalidProblemDefinitionException{"Dag needs one edge selection variable per edge"};

    auto n = _ns.size();
    for (const auto & [u, v] : _edges)
        if (u >= n || v >= n)
            throw InvalidProblemDefinitionException{"Dag has an edge endpoint that is not a node"};

    // The rows below read ns and es as Booleans, so both have to be in range
    // before anything is said about them.
    for (const auto & vars : {&_ns, &_es})
        for (const auto & v : *vars) {
            auto [lower, upper] = initial_state.bounds(v);
            if (lower < 0_i || upper > 1_i)
                throw InvalidProblemDefinitionException{"Dag needs its node and edge variables to be 0 or 1"};
        }

    // An edge list with no edges says nothing at all.
    return ! _edges.empty();
}

auto Dag::define_proof_model(ProofModel & model, const State &) -> void
{
    // MiniZinc's subgraph: a selected edge has both endpoints selected. This is
    // also what stops a walk running through an unselected node below, and it is
    // the half of the constraint fzn_dag leaves out; see the class documentation.
    for (size_t e = 0; e != _edges.size(); ++e) {
        model.add_labelled_constraint(
            _constraint_id, "sgf" + to_string(e), WPBSum{} + 1_i * (_ns[_edges[e].first] == 1_i) >= 1_i, HalfReifyOnConjunctionOf{{_es[e] == 1_i}});
        model.add_labelled_constraint(
            _constraint_id, "sgt" + to_string(e), WPBSum{} + 1_i * (_ns[_edges[e].second] == 1_i) >= 1_i, HalfReifyOnConjunctionOf{{_es[e] == 1_i}});
    }

    // The rest is the reachability ladder's breadth-first unfolding with the root
    // taken out: lev[v][k] says there is a selected walk of exactly k edges ending
    // at v. Acyclicity needs no anchor to unfold from, because a walk of as many
    // edges as there are nodes visits a node twice and so contains a cycle --- so
    // the constraint is simply that no such walk exists.
    //
    // Spreading the distance across a level flag each, rather than packing it into
    // one integer as fzn_dag does, is what makes the propagator's inferences plain
    // RUP: unit propagation over these rows walks round whatever cycle the
    // propagator found, one level per round, and arrives at the same contradiction.
    // It is also what removes the decomposition's per-edge products, because
    // nothing here has to *fix* a distance. See dev_docs/connectivity-proofs.md.
    //
    // Only the strongly connected components of the input graph get levels: an
    // edge between two of them cannot lie on a cycle. That makes the whole thing
    // free on an input that is already acyclic, and it is why the levels inside a
    // component count that component's nodes rather than the whole graph's.
    for (const auto & part : cyclic_parts_of(_ns.size(), _edges)) {
        auto levels = part.nodes.size() - 1;

        // Edges entering each node, held as positions within the component rather
        // than as edge numbers, so that the per-level arc flag vector below is as
        // long as the component's edge list and not as the whole graph's.
        vector<vector<size_t>> entering(_ns.size());
        for (size_t position = 0; position != part.edges.size(); ++position)
            entering[_edges[part.edges[position]].second].push_back(position);

        // Level zero is "the node is selected": a walk of no edges at all.
        vector<vector<ProofFlag>> lev(_ns.size());
        for (const auto & v : part.nodes)
            lev[v].push_back(model.create_proof_flag_fully_reifying(
                _constraint_id, {static_cast<long long>(v), 0}, "lev", WPBSum{} + 1_i * (_ns[v] == 1_i) >= 1_i));

        // Level k + 1: some selected edge inside the component leaves a node that
        // ends a walk of exactly k edges.
        for (size_t k = 0; k != levels; ++k) {
            vector<ProofFlag> arc_flags;
            arc_flags.reserve(part.edges.size());
            for (const auto & e : part.edges)
                arc_flags.push_back(model.create_proof_flag_fully_reifying(_constraint_id, {static_cast<long long>(e), static_cast<long long>(k)},
                    "arc", WPBSum{} + 1_i * (_es[e] == 1_i) + 1_i * lev[_edges[e].first][k] >= 2_i));

            for (const auto & v : part.nodes) {
                WPBSum support;
                for (const auto & position : entering[v])
                    support += 1_i * arc_flags[position];
                lev[v].push_back(model.create_proof_flag_fully_reifying(
                    _constraint_id, {static_cast<long long>(v), static_cast<long long>(k + 1)}, "lev", move(support) >= 1_i));
            }
        }

        // No walk of as many edges as the component has nodes, which is exactly
        // "no cycle": the longest simple path inside the component is one shorter.
        for (const auto & e : part.edges)
            model.add_labelled_constraint(_constraint_id, "nowalk" + to_string(e), WPBSum{} + 1_i * (_es[e] == 0_i) >= 1_i,
                HalfReifyOnConjunctionOf{{lev[_edges[e].first][levels]}});
    }
}

auto Dag::install_propagators(Propagators & propagators) -> void
{
    auto n = _ns.size();

    Triggers triggers;
    for (const auto & v : _ns)
        triggers.on_change.push_back(v);
    for (const auto & v : _es)
        triggers.on_change.push_back(v);

    propagators.install(
        constraint_id(),
        [n, edges = _edges, ns = _ns, es = _es, owner = constraint_id(), mutation = _proof_mutation](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            auto justify = JustifyUsingRUP{hints::Dag{owner}};
            auto fixed_to = [&](IntegerVariableID v, Integer x) {
                auto value = state.optional_single_value(v);
                return value && *value == x;
            };

            // Every reason below is guarded on inference.want_reasons(), as
            // propagator-performance.md asks: a ReasonLiterals element is large
            // enough that even the one-literal subgraph reasons are a memcpy, and
            // the cycle rule's is a walk back along a path. With proofs off nothing
            // reads any of them.
            auto reason_of = [&](auto && build) { return inference.want_reasons() ? Reason{ExplicitReason{build()}} : Reason{}; };

            // Subgraph, in both directions, exactly as Subgraph does it: a selected
            // edge selects its endpoints, and an edge with an unselected endpoint is
            // not selected. Each is RUP against the row for that edge and endpoint.
            auto one_literal = [&](const IntegerVariableCondition & lit) {
                ReasonLiterals lits{lit};
                if (holds_alternative<dag_proof_mutation::DropEndpointLiteral>(mutation))
                    lits.clear();
                return lits;
            };

            for (size_t e = 0; e != edges.size(); ++e) {
                auto [u, w] = edges[e];
                if (fixed_to(es[e], 1_i)) {
                    for (auto & endpoint : {u, w})
                        if (! fixed_to(ns[endpoint], 1_i))
                            inference.infer(logger, ns[endpoint] == 1_i, justify, reason_of([&] { return one_literal(es[e] == 1_i); }));
                }
                else if (! fixed_to(es[e], 0_i)) {
                    for (auto & endpoint : {u, w})
                        if (fixed_to(ns[endpoint], 0_i)) {
                            inference.infer(logger, es[e] == 0_i, justify, reason_of([&] { return one_literal(ns[endpoint] == 0_i); }));
                            break;
                        }
                }
            }

            // Acyclicity is downward closed, so nothing here is ever forced in, and
            // an edge has to go exactly when adding it to the edges already selected
            // would close a cycle. That is the whole of arc consistency: with every
            // undecided edge left out, what remains is what is already selected,
            // which is acyclic or the search would have failed already.
            //
            // The edges already selected, refreshed each call because the rows above
            // narrow domains as they go.
            vector<vector<pair<size_t, size_t>>> leaving(n);
            for (size_t e = 0; e != edges.size(); ++e)
                if (fixed_to(es[e], 1_i))
                    leaving[edges[e].first].emplace_back(edges[e].second, e);

            // Candidate edges grouped by head, so that one search from a head
            // answers for every edge that shares it. That is at most one search per
            // node rather than one per edge, and the searches can share their
            // buffers rather than each leaving a cached tree behind.
            vector<vector<size_t>> candidates(n);
            for (size_t e = 0; e != edges.size(); ++e) {
                if (fixed_to(es[e], 0_i))
                    continue;
                auto [u, v] = edges[e];

                // A self loop is a cycle all by itself, so the encoding rules it out
                // with no help: walking round it enough times overruns the levels
                // whatever else is selected. The reason is empty because there is
                // nothing to blame but the edge under discussion.
                // The reason is empty, so there is nothing here to guard.
                if (u == v)
                    inference.infer(logger, es[e] == 0_i, justify, ExplicitReason{ReasonLiterals{}});
                else
                    candidates[v].push_back(e);
            }

            vector<size_t> came_from(n), stack;
            vector<bool> seen(n);
            for (size_t v = 0; v != n; ++v) {
                if (candidates[v].empty())
                    continue;

                // Which nodes a selected path leaves v able to reach, and by which
                // edge each was first reached.
                seen.assign(n, false);
                came_from.assign(n, edges.size());
                stack.assign(1, v);
                seen[v] = true;
                while (! stack.empty()) {
                    auto at = stack.back();
                    stack.pop_back();
                    for (const auto & [w, f] : leaving[at])
                        if (! seen[w]) {
                            seen[w] = true;
                            came_from[w] = f;
                            stack.push_back(w);
                        }
                }

                for (const auto & e : candidates[v]) {
                    auto u = edges[e].first;
                    if (! seen[u])
                        continue;

                    // Walk the path back from u to v and blame each of its edges. If
                    // e is itself already selected this infers a 1 to be 0, which is
                    // the contradiction, raised with the same reason and the same one
                    // line.
                    inference.infer(logger, es[e] == 0_i, justify, reason_of([&] {
                        ReasonLiterals lits;
                        for (auto at = u; at != v;) {
                            auto f = came_from[at];
                            lits.push_back(es[f] == 1_i);
                            at = edges[f].first;
                        }
                        if (holds_alternative<dag_proof_mutation::DropPathEdge>(mutation) && ! lits.empty())
                            lits.pop_back();
                        return lits;
                    }));
                }
            }

            return PropagatorState::Enable;
        },
        triggers);
}
