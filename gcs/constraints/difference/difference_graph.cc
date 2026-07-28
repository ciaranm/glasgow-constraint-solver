#include <gcs/constraints/difference/difference_graph.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>

#include <util/overloaded.hh>

#include <optional>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::move;
using std::nullopt;
using std::optional;
using std::size_t;
using std::vector;

auto gcs::innards::deview_difference_operand(const IntegerVariableID & var) -> optional<DeviewedDifferenceOperand>
{
    return overloaded{
        [&](const SimpleIntegerVariableID & v) { return optional<DeviewedDifferenceOperand>{{v, 0_i}}; },                   //
        [&](const ConstantIntegerVariableID & v) { return optional<DeviewedDifferenceOperand>{{nullopt, v.const_value}}; }, //
        [&](const ViewOfIntegerVariableID & v) {
            if (v.negate_first)
                return optional<DeviewedDifferenceOperand>{nullopt};
            return optional<DeviewedDifferenceOperand>{{v.actual_variable, v.then_add}};
        } //
    }
        .visit(var);
}

auto gcs::innards::install_difference_propagator(Propagators & propagators, const ConstraintID & constraint_id, DifferenceGraph graph) -> void
{
    if (graph.edges.empty() && graph.static_bounds.empty())
        return;

    Triggers triggers;
    for (const auto & v : graph.nodes)
        triggers.on_bounds.emplace_back(v);

    propagators.install(
        constraint_id,
        [nodes = move(graph.nodes), graph_edges = move(graph.edges), static_bounds = move(graph.static_bounds), edge_lines = move(graph.edge_lines)](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            auto n = nodes.size();
            auto m = graph_edges.size();

            // Every pol below cites an edge row in deview mode. For rows this
            // constraint emitted itself that is a no-op: they are already over
            // bare variables, so no deview-form is registered for them and
            // deviewed_line_for hands the line straight back. It matters for a
            // presolver-built graph, whose rows belong to somebody else's
            // constraint and are therefore in the user's views' bits, while the
            // arithmetic here (and the reason literals) is over the canonical
            // bare variables. Same reasoning, and the same fix, as
            // linear/justify.cc.
            auto edge_line_pol = [&]() {
                PolBuilder pol;
                pol.enable_deview_mode(logger->names_and_ids_tracker());
                return pol;
            };

            // Static bounds first: an edge with a constant operand is a plain
            // bound on the other operand, and once applied it is just part of
            // the state that Bellman-Ford seeds from. These never change, so
            // after the first call every one of these is a no-op.
            for (const auto & sb : static_bounds) {
                if (sb.is_lower) {
                    if (state.lower_bound(nodes[sb.node]) < sb.value)
                        inference.infer_greater_than_or_equal(logger, nodes[sb.node], sb.value, JustifyUsingRUP{}, NoReason{});
                }
                else {
                    if (state.upper_bound(nodes[sb.node]) > sb.value)
                        inference.infer_less_than(logger, nodes[sb.node], sb.value + 1_i, JustifyUsingRUP{}, NoReason{});
                }
            }

            // Both passes walk a predecessor relation, one forwards along the
            // edges and one backwards, so each is parameterised by which end of
            // an edge the predecessor sits at. `head_of' is the node whose
            // bound the edge pushed (so pred[head_of(e)] == e), and `tail_of'
            // is the node whose bound was cited.

            // The refutation of a negative cycle is the sum of the cycle's edge
            // rows and nothing else: each variable appears once with +1 (as
            // some edge's head) and once with -1 (as the next edge's tail), so
            // every BinEnc term telescopes away and what is left is
            // `0 >= -(cycle weight)' with the right hand side at least 1. No
            // domain state is involved, hence the empty reason.
            //
            // Before saying anything, verify the extracted cycle
            // arithmetically: that each edge meets the next, that it closes,
            // and that the total weight really is negative. That is O(cycle)
            // and turns a predecessor-walk bug into an exception at the right
            // place rather than a VeriPB failure hundreds of lines later
            // (survey section 2.9.4).
            auto contradict_on_cycle = [&](const vector<size_t> & cycle, auto && tail_of, auto && head_of) -> void {
                if (cycle.empty())
                    throw UnexpectedException{"difference logic extracted an empty negative cycle"};
                Integer weight{0};
                for (size_t k = 0; k < cycle.size(); ++k) {
                    const auto & here = graph_edges[cycle[k]];
                    const auto & next = graph_edges[cycle[(k + 1) % cycle.size()]];
                    weight += here.d;
                    if (head_of(next) != tail_of(here))
                        throw UnexpectedException{"difference logic extracted a disconnected negative cycle"};
                }
                if (weight >= 0_i)
                    throw UnexpectedException{"difference logic extracted a cycle of weight " + weight.to_string() + ", which is not negative"};

                inference.contradiction(logger,
                    JustifyExplicitly{[&](const ReasonLiterals &) {
                                          auto pol = edge_line_pol();
                                          for (auto e : cycle)
                                              pol.add(edge_lines[graph_edges[e].posted_index]);
                                          pol.emit(*logger, ProofLevel::Temporary);
                                      },
                        ThenRUP::Yes},
                    NoReason{});
            };

            // Walk predecessors back from `start' looking for a cycle, which is
            // total: the walk cannot run off the end of the predecessor forest,
            // and whatever cycle it does reach is a negative one. Both are
            // proved in dev_docs/difference-logic.md ("Rounds, and why the
            // extraction is total"); in outline, a walk that reached a
            // predecessor-less node would exhibit a real path into `start'
            // whose source has held its seeded distance since before round 0,
            // and the round bound below says that path has already propagated,
            // contradicting the strict improvement that just happened.
            auto extract_cycle = [&](size_t start, const vector<optional<size_t>> & pred, auto && tail_of) -> vector<size_t> {
                vector<bool> seen(n, false);
                auto at = start;
                while (! seen[at]) {
                    seen[at] = true;
                    if (! pred[at])
                        throw UnexpectedException{"difference logic found no negative cycle where one must exist"};
                    at = tail_of(graph_edges[*pred[at]]);
                }

                vector<size_t> cycle;
                auto here = at;
                do {
                    cycle.push_back(*pred[here]);
                    here = tail_of(graph_edges[*pred[here]]);
                } while (here != at);
                return cycle;
            };

            // Infer improved bounds in an order consistent with the predecessor
            // forest, so that each node's push cites its predecessor's bound
            // *after* that bound has been applied. Roots of the forest are the
            // nodes whose bound did not improve, so every node with a
            // predecessor gets exactly one inference.
            auto infer_along_forest = [&](const vector<optional<size_t>> & pred, auto && tail_of, auto && infer_one) -> void {
                vector<bool> done(n, false);
                vector<size_t> chain;
                for (size_t v = 0; v < n; ++v) {
                    if (done[v] || ! pred[v])
                        continue;
                    chain.clear();
                    auto at = v;
                    while (! done[at] && pred[at]) {
                        done[at] = true;
                        chain.push_back(at);
                        at = tail_of(graph_edges[*pred[at]]);
                    }
                    for (auto it = chain.rbegin(); it != chain.rend(); ++it)
                        infer_one(*it);
                }
            };

            // Lower bounds flow forwards. Edge x --d--> y is x - y <= d, i.e.
            // y >= x - d, so lb(y) >= lb(x) - d. Writing dist(v) = -lb(v) this
            // is single-source shortest paths from the paper's dummy vertex v0,
            // whose edge to v weighs -lb(v): that is exactly how the seeding
            // below encodes the current bounds (Corollary 1).
            vector<Integer> lb(n, 0_i);
            vector<optional<size_t>> lb_pred(n, nullopt);
            for (size_t v = 0; v < n; ++v)
                lb[v] = state.lower_bound(nodes[v]);

            // A shortest path from v0 is simple, so after the seeding (which is
            // the v0 edge set) it uses at most n - 1 real edges, and n - 1
            // relaxation rounds suffice. Rounds 0 .. n - 1 give n of them, one
            // more than needed; round n relaxes nothing unless the system has a
            // negative cycle, so a success there is sound evidence of one and
            // the extraction above is guaranteed to find it.
            auto lb_tail_of = [](const DifferenceGraphEdge & g) { return g.from; };
            auto lb_head_of = [](const DifferenceGraphEdge & g) { return g.to; };

            for (size_t round = 0; round <= n; ++round) {
                bool changed = false;
                for (size_t e = 0; e < m; ++e) {
                    const auto & edge = graph_edges[e];
                    auto candidate = lb[edge.from] - edge.d;
                    if (candidate > lb[edge.to]) {
                        lb[edge.to] = candidate;
                        lb_pred[edge.to] = e;
                        changed = true;
                        if (round == n)
                            contradict_on_cycle(extract_cycle(edge.to, lb_pred, lb_tail_of), lb_tail_of, lb_head_of);
                    }
                }
                if (! changed)
                    break;
            }

            infer_along_forest(lb_pred, lb_tail_of, [&](size_t v) {
                const auto & edge = graph_edges[*lb_pred[v]];
                auto source = nodes[edge.from];
                auto source_lb = lb[edge.from];
                if (source_lb - edge.d != lb[v])
                    throw UnexpectedException{"difference logic lower bound does not match its predecessor edge"};
                if (state.lower_bound(nodes[v]) >= lb[v])
                    return;

                // One edge, one pol: the edge row plus the definition row
                // of the predecessor's bound literal cancels BinEnc(source)
                // and leaves BinEnc(v) >= source_lb - d, which is exactly
                // what the closing RUP needs. This is justify_linear_bounds
                // for a two-term linear, and it is the shape verified by
                // hand in boundpush_hand.pbp. Citing the predecessor's own
                // bound is already the paper's "lifted" explanation: the
                // weakest antecedent for v >= L - d across this edge *is*
                // source >= L, so the pol's degree comes out at exactly the
                // pushed amount with no wasted slack.
                inference.infer_greater_than_or_equal(logger, nodes[v], lb[v],
                    JustifyExplicitly{[&](const ReasonLiterals &) {
                                          auto pol = edge_line_pol();
                                          pol.add(edge_lines[edge.posted_index]);
                                          pol.add_for_literal(logger->names_and_ids_tracker(), source >= source_lb);
                                          pol.emit(*logger, ProofLevel::Temporary);
                                      },
                        ThenRUP::Yes},
                    ExplicitReason{ReasonLiterals{{source >= source_lb}}});
            });

            // Upper bounds flow backwards along the same edges. Edge
            // x --d--> y is also x <= y + d, so ub(x) <= ub(y) + d: shortest
            // paths in the reverse graph, seeded from the current upper bounds.
            vector<Integer> ub(n, 0_i);
            vector<optional<size_t>> ub_pred(n, nullopt);
            for (size_t v = 0; v < n; ++v)
                ub[v] = state.upper_bound(nodes[v]);

            auto ub_tail_of = [](const DifferenceGraphEdge & g) { return g.to; };
            auto ub_head_of = [](const DifferenceGraphEdge & g) { return g.from; };

            for (size_t round = 0; round <= n; ++round) {
                bool changed = false;
                for (size_t e = 0; e < m; ++e) {
                    const auto & edge = graph_edges[e];
                    auto candidate = ub[edge.to] + edge.d;
                    if (candidate < ub[edge.from]) {
                        ub[edge.from] = candidate;
                        ub_pred[edge.from] = e;
                        changed = true;
                        if (round == n)
                            contradict_on_cycle(extract_cycle(edge.from, ub_pred, ub_tail_of), ub_tail_of, ub_head_of);
                    }
                }
                if (! changed)
                    break;
            }

            infer_along_forest(ub_pred, ub_tail_of, [&](size_t v) {
                const auto & edge = graph_edges[*ub_pred[v]];
                auto source = nodes[edge.to];
                auto source_ub = ub[edge.to];
                if (source_ub + edge.d != ub[v])
                    throw UnexpectedException{"difference logic upper bound does not match its predecessor edge"};
                if (state.upper_bound(nodes[v]) <= ub[v])
                    return;

                inference.infer_less_than(logger, nodes[v], ub[v] + 1_i,
                    JustifyExplicitly{[&](const ReasonLiterals &) {
                                          auto pol = edge_line_pol();
                                          pol.add(edge_lines[edge.posted_index]);
                                          pol.add_for_literal(logger->names_and_ids_tracker(), source < source_ub + 1_i);
                                          pol.emit(*logger, ProofLevel::Temporary);
                                      },
                        ThenRUP::Yes},
                    ExplicitReason{ReasonLiterals{{source < source_ub + 1_i}}});
            });

            // Deliberately not EnableButIdempotent, and not merely because the
            // scope aliases whenever one variable appears in several edges
            // (which is the normal case here, and which Propagators::install
            // detects and ignores the claim for anyway). The claim would be
            // wrong on its own terms: the passes above reach the fixpoint of
            // the bounds abstraction, but an inferred bound can snap past a
            // hole in the domain and land strictly above the value computed
            // here, which seeds the next call higher and lets it push further.
            // So a second call genuinely can infer more, and the propagator has
            // to be re-woken by its own inferences until the state settles.
            // (run_hole_snap_test in difference_constraints_test.cc pins this.)
            return PropagatorState::Enable;
        },
        triggers);
}
