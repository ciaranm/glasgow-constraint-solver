#include <gcs/constraints/reachable/hints.hh>
#include <gcs/constraints/reachable/reachable.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <variant>

#include <algorithm>
#include <memory>
#include <optional>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::innards::reachable;

using std::holds_alternative;
using std::make_unique;
using std::min;
using std::move;
using std::pair;
using std::size_t;
using std::string;
using std::to_string;
using std::unique_ptr;
using std::vector;
using std::ranges::all_of;

namespace
{
    // An arc is an edge together with the direction it may be followed in. An
    // undirected graph gives two arcs per edge, a directed graph one.
    struct Arc
    {
        size_t edge;
        size_t from;
        size_t to;
    };

    auto arcs_of(const vector<pair<size_t, size_t>> & edges, bool directed) -> vector<Arc>
    {
        vector<Arc> arcs;
        arcs.reserve(directed ? edges.size() : 2 * edges.size());
        for (size_t e = 0; e != edges.size(); ++e) {
            arcs.push_back(Arc{e, edges[e].first, edges[e].second});
            if (! directed)
                arcs.push_back(Arc{e, edges[e].second, edges[e].first});
        }
        return arcs;
    }

    // Arc indices leaving and entering each node, so a search does not have to
    // rescan the whole arc list per node.
    struct Adjacency
    {
        vector<vector<size_t>> leaving, entering;
    };

    auto adjacency_of(size_t n, const vector<Arc> & arcs) -> Adjacency
    {
        Adjacency adj{vector<vector<size_t>>(n), vector<vector<size_t>>(n)};
        for (size_t a = 0; a != arcs.size(); ++a) {
            adj.leaving[arcs[a].from].push_back(a);
            adj.entering[arcs[a].to].push_back(a);
        }
        return adj;
    }
}

ReachableBase::ReachableBase(vector<pair<size_t, size_t>> edges, IntegerVariableID root, vector<IntegerVariableID> ns, vector<IntegerVariableID> es,
    bool directed) : _edges(move(edges)), _root(root), _ns(move(ns)), _es(move(es)), _directed(directed)
{
}

auto ReachableBase::with_cut_forcing(std::optional<bool> enable) -> ReachableBase &
{
    if (enable)
        _cut_forcing = *enable;
    return *this;
}

auto ReachableBase::with_proof_mutation(ReachableProofMutation mutation) -> ReachableBase &
{
    _proof_mutation = mutation;
    return *this;
}

auto ReachableBase::prepare(Propagators & propagators, State & initial_state, ProofModel * const model) -> bool
{
    if (_ns.empty())
        throw InvalidProblemDefinitionException{"Reachable needs at least one node: the root has to be a node, and has to be selected"};
    if (_edges.size() != _es.size())
        throw InvalidProblemDefinitionException{"Reachable needs one edge selection variable per edge"};

    auto n = _ns.size();
    for (const auto & [u, v] : _edges)
        if (u >= n || v >= n)
            throw InvalidProblemDefinitionException{"Reachable has an edge endpoint that is not a node"};

    // The OPB encoding reads ns and es as Booleans, and pins "the root is node v"
    // to exactly one v, so both have to be within range before anything is said
    // about them.
    for (const auto & vars : {&_ns, &_es})
        for (const auto & v : *vars) {
            auto [lower, upper] = initial_state.bounds(v);
            if (lower < 0_i || upper > 1_i)
                throw InvalidProblemDefinitionException{"Reachable needs its node and edge variables to be 0 or 1"};
        }

    // The root is a node number, which is part of what the constraint says rather
    // than something the caller has to have arranged: MiniZinc's `dreachable` has
    // ns[r] in it, so an r that does not index ns is simply false. Defining the
    // bound rather than throwing also means the OPB's "exactly one node is the
    // root" row has something to stand on.
    propagators.define_bound(initial_state, model, _root, Bound::Lower, 0_i);
    propagators.define_bound(initial_state, model, _root, Bound::Upper, Integer(static_cast<long long>(n) - 1));

    return true;
}

auto ReachableBase::define_proof_model(ProofModel & model, const State &) -> void
{
    auto n = _ns.size();
    auto arcs = arcs_of(_edges, _directed);
    auto adj = adjacency_of(n, arcs);

    // MiniZinc's subgraph: a selected edge has both endpoints selected. Every
    // other row below leans on this, because it is what stops a walk running
    // through an unselected node.
    for (size_t e = 0; e != _edges.size(); ++e) {
        model.add_labelled_constraint(
            _constraint_id, "sgf" + to_string(e), WPBSum{} + 1_i * (_ns[_edges[e].first] == 1_i) >= 1_i, HalfReifyOnConjunctionOf{{_es[e] == 1_i}});
        model.add_labelled_constraint(
            _constraint_id, "sgt" + to_string(e), WPBSum{} + 1_i * (_ns[_edges[e].second] == 1_i) >= 1_i, HalfReifyOnConjunctionOf{{_es[e] == 1_i}});
    }

    // The rest is a breadth-first unfolding of "reachable from the root":
    // reach[v][k] says node v is reached within k steps. Encoding it a step at a
    // time, rather than as the stdlib's arithmetic distance labelling, is what
    // makes the propagator's inferences plain RUP -- unit propagation over these
    // rows *is* the breadth-first search the propagator runs, so it reproduces
    // whatever the propagator concluded. See dev_docs/connectivity-proofs.md.
    //
    // The cost is size: the unfolding needs one level per possible step, so it
    // is O(nodes * edges) rows rather than the decomposition's O(edges).

    // Level zero: reach[v][0] is "the root is v". These flags are also what pins
    // the root down for the proof: exactly one of them holds, whatever encoding
    // the root variable itself has.
    vector<vector<ProofFlag>> reach(n);
    WPBSum exactly_one_root;
    for (size_t v = 0; v != n; ++v) {
        auto is_root = model.create_proof_flag_fully_reifying(
            _constraint_id, {static_cast<long long>(v)}, "root", WPBSum{} + 1_i * (_root == Integer(static_cast<long long>(v))) >= 1_i);
        reach[v].push_back(is_root);
        exactly_one_root += 1_i * is_root;
        // ns[r]: the root is a selected node, so the subgraph is never empty.
        model.add_labelled_constraint(
            _constraint_id, "rootin" + to_string(v), WPBSum{} + 1_i * (_ns[v] == 1_i) >= 1_i, HalfReifyOnConjunctionOf{{is_root}});
    }
    model.add_labelled_constraint(_constraint_id, "root1le", "root1ge", move(exactly_one_root) == 1_i);

    // Level k: reach[v][k] iff v was already reached, or some selected arc into v
    // leaves a node that was reached one step sooner.
    auto levels = n - 1;
    for (size_t k = 1; k <= levels; ++k) {
        vector<ProofFlag> arc_flags;
        arc_flags.reserve(arcs.size());
        for (size_t a = 0; a != arcs.size(); ++a)
            arc_flags.push_back(model.create_proof_flag_fully_reifying(_constraint_id, {static_cast<long long>(a), static_cast<long long>(k)}, "arc",
                WPBSum{} + 1_i * (_es[arcs[a].edge] == 1_i) + 1_i * reach[arcs[a].from][k - 1] >= 2_i));

        for (size_t v = 0; v != n; ++v) {
            WPBSum support;
            support += 1_i * reach[v][k - 1];
            for (const auto & a : adj.entering[v])
                support += 1_i * arc_flags[a];
            reach[v].push_back(model.create_proof_flag_fully_reifying(
                _constraint_id, {static_cast<long long>(v), static_cast<long long>(k)}, "reach", move(support) >= 1_i));
        }
    }

    // Every selected node is reached. A walk in an n-node graph never needs more
    // than n - 1 steps, so this is reachability and not an approximation of it.
    for (size_t v = 0; v != n; ++v)
        model.add_labelled_constraint(
            _constraint_id, "reached" + to_string(v), WPBSum{} + 1_i * reach[v][levels] >= 1_i, HalfReifyOnConjunctionOf{{_ns[v] == 1_i}});
}

auto ReachableBase::install_propagators(Propagators & propagators) -> void
{
    auto n = _ns.size();
    auto arcs = arcs_of(_edges, _directed);
    auto adj = adjacency_of(n, arcs);

    Triggers triggers;
    for (const auto & v : _ns)
        triggers.on_change.push_back(v);
    for (const auto & v : _es)
        triggers.on_change.push_back(v);
    triggers.on_change.push_back(_root);

    propagators.install(
        constraint_id(),
        [n, edges = _edges, ns = _ns, es = _es, root = _root, arcs = move(arcs), adj = move(adj), owner = constraint_id(), directed = _directed,
            cut_forcing = _cut_forcing,
            mutation = _proof_mutation](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            auto justify = JustifyUsingRUP{hints::Reachable{owner}};
            auto fixed_to = [&](IntegerVariableID v, Integer x) {
                auto value = state.optional_single_value(v);
                return value && *value == x;
            };

            // Subgraph: a selected edge has both endpoints selected, and an edge
            // with an unselected endpoint is not selected.
            for (size_t e = 0; e != edges.size(); ++e) {
                auto [u, w] = edges[e];
                if (fixed_to(es[e], 1_i)) {
                    for (auto & endpoint : {u, w})
                        if (! fixed_to(ns[endpoint], 1_i))
                            inference.infer(logger, ns[endpoint] == 1_i, justify, ExplicitReason{ReasonLiterals{es[e] == 1_i}});
                }
                else if (! fixed_to(es[e], 0_i)) {
                    for (auto & endpoint : {u, w})
                        if (fixed_to(ns[endpoint], 0_i)) {
                            inference.infer(logger, es[e] == 0_i, justify, ExplicitReason{ReasonLiterals{ns[endpoint] == 0_i}});
                            break;
                        }
                }
            }

            // The root is a selected node, in both directions.
            auto node_of = [&](Integer rho) -> size_t { return static_cast<size_t>(rho.raw_value); };
            auto is_node = [&](Integer rho) { return rho >= 0_i && rho < Integer(static_cast<long long>(n)); };

            vector<Integer> drop;
            state.for_each_value_immutable(root, [&](Integer rho) {
                if (is_node(rho) && fixed_to(ns[node_of(rho)], 0_i))
                    drop.push_back(rho);
            });
            for (const auto & rho : drop)
                inference.infer(logger, root != rho, justify, ExplicitReason{ReasonLiterals{ns[node_of(rho)] == 0_i}});

            if (auto fixed_root = state.optional_single_value(root); fixed_root && is_node(*fixed_root)) {
                auto r = node_of(*fixed_root);
                if (! fixed_to(ns[r], 1_i))
                    inference.infer(logger, ns[r] == 1_i, justify, ExplicitReason{ReasonLiterals{root == *fixed_root}});
            }

            // What is left of the graph: nodes and edges not yet ruled out. Every
            // reachability claim below is made over this, so a claim stays true as
            // the search goes deeper. It is refreshed rather than computed once,
            // because the rules above narrow domains as they go.
            //
            // One node or one edge may additionally be treated as though it were
            // out, for the "suppose this were not selected" searches the forcing
            // rules make. Such a thing is undecided rather than ruled out, so the
            // border reasons below know not to blame it: the step that uses them
            // supplies it from its own negated goal instead.
            auto no_node = n, no_edge = edges.size();
            auto hypothetical_node = no_node, hypothetical_edge = no_edge;
            vector<bool> node_out(n, false), arc_out(arcs.size(), false);
            auto refresh_graph = [&]() {
                for (size_t v = 0; v != n; ++v)
                    node_out[v] = fixed_to(ns[v], 0_i);
                for (size_t a = 0; a != arcs.size(); ++a)
                    arc_out[a] = fixed_to(es[arcs[a].edge], 0_i) || node_out[arcs[a].from] || node_out[arcs[a].to];
            };
            refresh_graph();

            auto node_usable = [&](size_t v) { return ! node_out[v] && v != hypothetical_node; };
            auto arc_usable = [&](size_t a) {
                return ! arc_out[a] && arcs[a].edge != hypothetical_edge && arcs[a].from != hypothetical_node && arcs[a].to != hypothetical_node;
            };

            // Nodes reachable from `sources`, and nodes that can reach `target`.
            auto search = [&](const vector<size_t> & sources, bool forwards) {
                vector<bool> seen(n, false);
                vector<size_t> stack;
                for (const auto & s : sources)
                    if (node_usable(s) && ! seen[s]) {
                        seen[s] = true;
                        stack.push_back(s);
                    }
                while (! stack.empty()) {
                    auto v = stack.back();
                    stack.pop_back();
                    for (const auto & a : forwards ? adj.leaving[v] : adj.entering[v]) {
                        auto next = forwards ? arcs[a].to : arcs[a].from;
                        if (arc_usable(a) && ! seen[next]) {
                            seen[next] = true;
                            stack.push_back(next);
                        }
                    }
                }
                return seen;
            };

            // The literals that shut the border of `inside` -- which the search
            // above leaves closed under usable arcs, so every arc across the border
            // really is ruled out, and one of these literals says why. This is the
            // whole reason: unit propagation over the encoding's levels replays the
            // same search from these literals, which is why a plain RUP suffices.
            auto border_reason = [&](const vector<bool> & inside, bool forwards) {
                ReasonLiterals lits;
                vector<bool> node_said(n, false), edge_said(edges.size(), false);
                for (size_t v = 0; v != n; ++v) {
                    if (! inside[v])
                        continue;
                    for (const auto & a : forwards ? adj.leaving[v] : adj.entering[v]) {
                        auto outside = forwards ? arcs[a].to : arcs[a].from;
                        if (inside[outside])
                            continue;
                        // A genuine blocker gets named; an arc stopped only by the
                        // hypothesis does not, because it is the caller's negated
                        // goal that supplies it.
                        if (fixed_to(es[arcs[a].edge], 0_i)) {
                            if (! edge_said[arcs[a].edge]) {
                                edge_said[arcs[a].edge] = true;
                                lits.push_back(es[arcs[a].edge] == 0_i);
                            }
                        }
                        else if (node_out[outside] && ! node_said[outside]) {
                            node_said[outside] = true;
                            lits.push_back(ns[outside] == 0_i);
                        }
                    }
                }
                if (holds_alternative<reachable_proof_mutation::DropBorderLiteral>(mutation) && ! lits.empty())
                    lits.pop_back();
                return lits;
            };

            // The root has to be able to reach every selected node, so a candidate
            // root that cannot is not the root. Searching backwards from the
            // selected node gives every such candidate at once, under one reason.
            vector<bool> covered(n, false);
            for (size_t m = 0; m != n; ++m) {
                if (! fixed_to(ns[m], 1_i) || covered[m])
                    continue;
                auto can_reach_m = search({m}, false);
                // Undirected, "can reach m" is m's whole component, so every other
                // selected node in it would repeat this search and reach the same
                // verdict under the same reason. Directed, the sets genuinely
                // differ, and each selected node has to be asked separately.
                if (! directed)
                    for (size_t u = 0; u != n; ++u)
                        if (can_reach_m[u])
                            covered[u] = true;
                drop.clear();
                state.for_each_value_immutable(root, [&](Integer rho) {
                    if (! is_node(rho) || ! can_reach_m[node_of(rho)])
                        drop.push_back(rho);
                });
                if (drop.empty())
                    continue;
                auto lits = border_reason(can_reach_m, false);
                if (! holds_alternative<reachable_proof_mutation::DropMandatoryNode>(mutation))
                    lits.push_back(ns[m] == 1_i);
                for (const auto & rho : drop)
                    inference.infer(logger, root != rho, justify, ExplicitReason{lits});
            }

            // Nothing the root can no longer reach can be selected.
            vector<size_t> candidates;
            state.for_each_value_immutable(root, [&](Integer rho) {
                if (is_node(rho))
                    candidates.push_back(node_of(rho));
            });
            auto reached = search(candidates, true);

            // The reason is stated per unreachable *region* rather than per node,
            // and against the region rather than against everything the root has
            // lost. What the replay needs, to falsify a node's top level, is that
            // every node that could still walk *to* it is dead at level zero and
            // sealed off; nodes that could not walk to it never enter the argument.
            // So the backward-reachable set from an unreachable node is the whole
            // support: nothing outside it can get in (or it would be in it), the
            // root's domain lies inside the reached region so none of it is a
            // candidate root, and every node in it is ruled out under the same
            // literals. On a graph with a large reached region and a small cut-off
            // piece --- which is what connectivity search mostly produces --- that
            // is a reason the size of the piece, not of the graph.
            vector<bool> handled(n, false);
            for (size_t v = 0; v != n; ++v) {
                if (node_out[v] || reached[v] || handled[v])
                    continue;

                auto region = search({v}, false);
                auto lits = border_reason(region, false);
                if (! holds_alternative<reachable_proof_mutation::DropRootDomain>(mutation))
                    for (size_t u = 0; u != n; ++u)
                        if (region[u])
                            lits.push_back(root != Integer(static_cast<long long>(u)));

                for (size_t u = 0; u != n; ++u)
                    if (region[u] && ! node_out[u] && ! reached[u]) {
                        handled[u] = true;
                        inference.infer(logger, ns[u] == 0_i, justify, ExplicitReason{lits});
                    }
            }

            // Cut vertices and bridges: a node or edge that every remaining
            // solution has to use. This is the only place this constraint forces
            // something *in*, and it is exactly the rest of generalised arc
            // consistency --- see dev_docs/connectivity-proofs.md.
            if (! cut_forcing)
                return PropagatorState::Enable;

            refresh_graph();

            vector<bool> selected(n, false), candidate(n, false);
            vector<size_t> mandatory, roots;
            for (size_t v = 0; v != n; ++v)
                if (! node_out[v] && fixed_to(ns[v], 1_i)) {
                    selected[v] = true;
                    mandatory.push_back(v);
                }
            state.for_each_value_immutable(root, [&](Integer rho) {
                if (is_node(rho) && ! node_out[node_of(rho)]) {
                    candidate[node_of(rho)] = true;
                    roots.push_back(node_of(rho));
                }
            });
            if (mandatory.empty() || roots.empty())
                return PropagatorState::Enable;

            // Justify forcing `goal` in, given that taking it out leaves no
            // candidate root able to reach every selected node. With the root
            // already decided that is one RUP: unit propagation starts at the root,
            // walks what is left, and arrives at a selected node it cannot reach.
            // With the root still open the same argument has to be made once per
            // candidate, since unit propagation cannot case-split over which node
            // the root is; the closing step then has no root left to use.
            auto force_in = [&](const IntegerVariableCondition & goal, size_t hyp_node, size_t hyp_edge) {
                hypothetical_node = hyp_node;
                hypothetical_edge = hyp_edge;

                ReasonLiterals lits;
                vector<bool> covered_by_a_piece(n, false);
                vector<Integer> to_rule_out;
                for (const auto & rho : roots) {
                    if (rho == hyp_node)
                        continue; // taking it out already says the root is elsewhere
                    to_rule_out.push_back(Integer(static_cast<long long>(rho)));
                    if (covered_by_a_piece[rho])
                        continue;
                    auto piece = search({rho}, true);
                    // Undirected, everything this candidate reaches would reach the
                    // same set back, so one border seals the argument for all of
                    // them. Directed it would not: a candidate inside this piece
                    // reaches only part of it, and needs its own border.
                    if (! directed)
                        for (size_t u = 0; u != n; ++u)
                            if (piece[u])
                                covered_by_a_piece[u] = true;
                    auto piece_lits = border_reason(piece, true);
                    lits.insert(lits.end(), piece_lits.begin(), piece_lits.end());
                    for (const auto & m : mandatory)
                        if (! piece[m]) {
                            lits.push_back(ns[m] == 1_i);
                            break;
                        }
                }

                hypothetical_node = no_node;
                hypothetical_edge = no_edge;

                // With the root already decided this is one RUP: the reason names
                // it, and unit propagation has the one place to start from that the
                // whole argument needs.
                if (auto fixed_root = state.optional_single_value(root); fixed_root && node_of(*fixed_root) != hyp_node) {
                    lits.push_back(root == *fixed_root);
                    inference.infer(logger, goal, justify, ExplicitReason{move(lits)});
                    return;
                }

                for (long long sigma = 0; sigma != static_cast<long long>(n); ++sigma)
                    if (! state.in_domain(root, Integer{sigma}))
                        lits.push_back(root != Integer{sigma});

                auto emit = [&, goal, to_rule_out](const ReasonLiterals & reason_lits) {
                    for (const auto & rho : to_rule_out)
                        logger->emit_rup_proof_line_under_reason(
                            reason_lits, WPBSum{} + 1_i * goal + 1_i * (root != rho) >= 1_i, ProofLevel::Temporary);
                };
                inference.infer(logger, goal, JustifyExplicitly{emit, ThenRUP::Yes, hints::Reachable{owner}}, ExplicitReason{move(lits)});
            };

            if (directed) {
                // The directed analogue of a cut vertex is a dominator, and because
                // the root is existentially quantified the selected node that
                // witnesses it may differ from one candidate root to the next --- so
                // there is no single dominator tree that answers this, and no
                // one-pass version at all (the doc spells out why). This asks the
                // question directly instead, which is exact but costs a search per
                // candidate root per node and edge. It is the reason
                // with_cut_forcing() exists as a switch.
                auto survives_without = [&](size_t hyp_node, size_t hyp_edge) {
                    hypothetical_node = hyp_node;
                    hypothetical_edge = hyp_edge;
                    auto survives = false;
                    for (const auto & rho : roots) {
                        if (rho == hyp_node)
                            continue;
                        auto reached_from_rho = search({rho}, true);
                        if (all_of(mandatory.begin(), mandatory.end(), [&](size_t m) { return reached_from_rho[m]; })) {
                            survives = true;
                            break;
                        }
                    }
                    hypothetical_node = no_node;
                    hypothetical_edge = no_edge;
                    return survives;
                };

                for (size_t v = 0; v != n; ++v)
                    if (! node_out[v] && ! selected[v] && ! survives_without(v, no_edge))
                        force_in(ns[v] == 1_i, v, no_edge);

                for (size_t e = 0; e != edges.size(); ++e)
                    if (! state.optional_single_value(es[e]) && ! survives_without(no_node, e))
                        force_in(es[e] == 1_i, no_node, e);

                return PropagatorState::Enable;
            }

            // The rules above leave every selected node and every candidate root in
            // one component. If they have not reached that fixpoint yet there is
            // nothing here to say, and they will fire again before there is.
            auto component = search({mandatory.front()}, true);
            for (const auto & v : mandatory)
                if (! component[v])
                    return PropagatorState::Enable;
            for (const auto & v : roots)
                if (! component[v])
                    return PropagatorState::Enable;

            // One depth-first pass over that component gives the articulation
            // points and the bridges together, and carries the counts that say
            // whether removing one would actually separate anything: a piece is
            // survivable exactly when it holds every selected node and at least one
            // candidate root.
            vector<int> disc(n, -1), low(n, 0), selected_below(n, 0), candidates_below(n, 0);
            vector<size_t> entered_by(n, no_edge);
            vector<bool> skipped_entry(n, false);
            vector<vector<size_t>> separated_children(n);
            vector<pair<size_t, size_t>> bridges; // (edge, the child endpoint)
            vector<pair<size_t, size_t>> dfs;
            int timer = 0;
            auto visit = [&](size_t v) {
                disc[v] = low[v] = timer++;
                selected_below[v] = selected[v] ? 1 : 0;
                candidates_below[v] = candidate[v] ? 1 : 0;
                dfs.emplace_back(v, 0);
            };
            visit(mandatory.front());
            while (! dfs.empty()) {
                auto v = dfs.back().first;
                if (dfs.back().second < adj.leaving[v].size()) {
                    auto a = adj.leaving[v][dfs.back().second++];
                    if (! arc_usable(a))
                        continue;
                    // Skip one copy of the edge this vertex was entered by --- by
                    // edge and not by vertex, so a parallel edge is still seen and
                    // correctly stops either of them being a bridge.
                    if (arcs[a].edge == entered_by[v] && ! skipped_entry[v]) {
                        skipped_entry[v] = true;
                        continue;
                    }
                    auto w = arcs[a].to;
                    if (disc[w] == -1) {
                        entered_by[w] = arcs[a].edge;
                        visit(w);
                    }
                    else
                        low[v] = min(low[v], disc[w]);
                }
                else {
                    dfs.pop_back();
                    if (! dfs.empty()) {
                        auto u = dfs.back().first;
                        low[u] = min(low[u], low[v]);
                        selected_below[u] += selected_below[v];
                        candidates_below[u] += candidates_below[v];
                        if (low[v] >= disc[u])
                            separated_children[u].push_back(v);
                        if (low[v] > disc[u])
                            bridges.emplace_back(entered_by[v], v);
                    }
                }
            }

            auto total_selected = selected_below[mandatory.front()];
            auto total_candidates = candidates_below[mandatory.front()];
            auto piece_survives = [&](int has_selected, int has_candidates) { return has_selected == total_selected && has_candidates >= 1; };

            for (size_t v = 0; v != n; ++v) {
                if (node_out[v] || selected[v] || disc[v] == -1 || v == mandatory.front())
                    continue;
                auto separated_selected = 0, separated_candidates = 0;
                auto survives = false;
                for (const auto & c : separated_children[v]) {
                    separated_selected += selected_below[c];
                    separated_candidates += candidates_below[c];
                    if (piece_survives(selected_below[c], candidates_below[c]))
                        survives = true;
                }
                if (piece_survives(total_selected - separated_selected, total_candidates - (candidate[v] ? 1 : 0) - separated_candidates))
                    survives = true;
                if (! survives)
                    force_in(ns[v] == 1_i, v, no_edge);
            }

            for (const auto & [e, child] : bridges) {
                if (state.optional_single_value(es[e]))
                    continue;
                if (piece_survives(selected_below[child], candidates_below[child]))
                    continue;
                if (piece_survives(total_selected - selected_below[child], total_candidates - candidates_below[child]))
                    continue;
                force_in(es[e] == 1_i, no_node, e);
            }

            return PropagatorState::Enable;
        },
        triggers);
}

auto ReachableBase::base_s_expr(const ProofModel * const model) const -> SExpr
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
        tracker.s_expr_term_of(_root), SExpr::list(move(ns)), SExpr::list(move(es))});
}

Reachable::Reachable(vector<pair<size_t, size_t>> edges, IntegerVariableID root, vector<IntegerVariableID> ns, vector<IntegerVariableID> es) :
    ReachableBase(move(edges), root, move(ns), move(es), false)
{
}

auto Reachable::clone() const -> unique_ptr<Constraint>
{
    auto copy = make_unique<Reachable>(_edges, _root, _ns, _es);
    copy->with_cut_forcing(_cut_forcing);
    copy->with_proof_mutation(_proof_mutation);
    return copy;
}

auto Reachable::constraint_type() const -> string
{
    return "reachable";
}

auto Reachable::s_expr(const ProofModel * const model) const -> SExpr
{
    return base_s_expr(model);
}

DReachable::DReachable(vector<pair<size_t, size_t>> edges, IntegerVariableID root, vector<IntegerVariableID> ns, vector<IntegerVariableID> es) :
    ReachableBase(move(edges), root, move(ns), move(es), true)
{
}

auto DReachable::clone() const -> unique_ptr<Constraint>
{
    auto copy = make_unique<DReachable>(_edges, _root, _ns, _es);
    copy->with_cut_forcing(_cut_forcing);
    copy->with_proof_mutation(_proof_mutation);
    return copy;
}

auto DReachable::constraint_type() const -> string
{
    return "dreachable";
}

auto DReachable::s_expr(const ProofModel * const model) const -> SExpr
{
    return base_s_expr(model);
}
