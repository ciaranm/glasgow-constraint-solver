#include <gcs/constraints/difference/difference_constraints.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <util/overloaded.hh>

#include <map>
#include <memory>
#include <string>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::map;
using std::move;
using std::nullopt;
using std::optional;
using std::size_t;
using std::string;
using std::to_string;
using std::unique_ptr;
using std::vector;

namespace
{
    // Reduce an operand to (bare variable, offset), so that V = *variable +
    // offset. A constant operand has no variable, just the offset.
    //
    // A negated view is rejected outright: V - W <= d with V = -X + c is
    // -X - W <= d - c, which is not a difference constraint (both coefficients
    // are negative). Getting this wrong is unsound rather than merely
    // incomplete, so it is a hard error at construction. See the survey's
    // section 2.6(e).
    struct DeviewedOperand
    {
        optional<SimpleIntegerVariableID> variable;
        Integer offset;
    };

    auto deview_operand(const IntegerVariableID & var, const char * which) -> DeviewedOperand
    {
        return overloaded{
            [&](const SimpleIntegerVariableID & v) { return DeviewedOperand{v, 0_i}; },                   //
            [&](const ConstantIntegerVariableID & v) { return DeviewedOperand{nullopt, v.const_value}; }, //
            [&](const ViewOfIntegerVariableID & v) {
                if (v.negate_first)
                    throw InvalidProblemDefinitionException{
                        string{"DifferenceConstraints "} + which + " operand is a negated view, which is not a difference constraint"};
                return DeviewedOperand{v.actual_variable, v.then_add};
            } //
        }
            .visit(var);
    }
}

DifferenceConstraints::DifferenceConstraints(vector<DifferenceEdge> edges) : _edges(move(edges))
{
    // Reject negated views up front, so a bad model is a post-time error rather
    // than a mysterious proof failure much later. prepare() redoes the
    // deviewing; this is a cheap guard, not the canonicalisation itself.
    for (const auto & e : _edges) {
        static_cast<void>(deview_operand(e.x, "left"));
        static_cast<void>(deview_operand(e.y, "right"));
    }
}

auto DifferenceConstraints::clone() const -> unique_ptr<Constraint>
{
    return make_unique<DifferenceConstraints>(_edges);
}

auto DifferenceConstraints::prepare(Propagators &, State &, ProofModel * const) -> bool
{
    if (_edges.empty())
        return false;

    map<SimpleIntegerVariableID, size_t> node_of;
    auto node_index = [&](const SimpleIntegerVariableID & v) -> size_t {
        auto [it, inserted] = node_of.emplace(v, _nodes.size());
        if (inserted)
            _nodes.push_back(v);
        return it->second;
    };

    for (size_t i = 0; i < _edges.size(); ++i) {
        const auto & e = _edges[i];
        auto left = deview_operand(e.x, "left");
        auto right = deview_operand(e.y, "right");

        // (X + c1) - (Y + c2) <= d  becomes  X - Y <= d - c1 + c2, so every
        // edge's weight is expressed over bare variables and nothing else.
        auto d = e.d - left.offset + right.offset;

        if (left.variable && right.variable) {
            auto from = node_index(*left.variable);
            auto to = node_index(*right.variable);
            if (from == to) {
                // Aliasing: X - X <= d, i.e. 0 <= d. Vacuous when d >= 0, a
                // root contradiction when d < 0 (the OPB row is directly
                // false, so the contradiction RUPs from it).
                if (d < 0_i && ! _root_contradiction_posted_index)
                    _root_contradiction_posted_index = i;
            }
            else
                _graph_edges.push_back(GraphEdge{from, to, d, i});
        }
        else if (left.variable) {
            // X - c2 <= d, i.e. X <= d (c2 already folded in above).
            _static_bounds.push_back(StaticBound{node_index(*left.variable), d, false, i});
        }
        else if (right.variable) {
            // c1 - Y <= d, i.e. Y >= -d.
            _static_bounds.push_back(StaticBound{node_index(*right.variable), -d, true, i});
        }
        else {
            // Two constants: 0 <= d, exactly as for aliasing.
            if (d < 0_i && ! _root_contradiction_posted_index)
                _root_contradiction_posted_index = i;
        }
    }

    return true;
}

auto DifferenceConstraints::define_proof_model(ProofModel & model, const State &) -> void
{
    // One labelled row per posted edge, role e<i> with i the edge's position in
    // the posted list, so a proof line can be traced back to the edge the user
    // wrote. Nothing else goes in: no flags, no auxiliaries. Every inference
    // this constraint makes is a cutting-planes consequence of these rows.
    //
    // The row is emitted over the *canonical* (deviewed) operands, with the
    // views' offsets folded into the right hand side, rather than over the
    // user's operands. This is deliberate, and it is what makes the proofs
    // work: the negative-cycle refutation and the bound pushes both rely on
    // consecutive edges' shared variable cancelling exactly, and
    // dev_docs/view-proof-logging.md invariant 1 says that only happens when
    // both rows express it in the same representation. A registered view V of X
    // has its own bit-vector, related to BinEnc(X) only by the link axiom, so
    // two edges meeting at "the same variable" through different views would
    // not cancel at all. Emitting the deviewed form removes the problem by
    // construction, and it is still definitional: X - Y <= d - c1 + c2 states
    // exactly the posted V1 - V2 <= d, just written in the bare variables'
    // bits. (The alternative would be to emit in the user's operands and use
    // PolBuilder::enable_deview_mode, as linear/justify.cc does; that is
    // strictly more machinery for the same result here, since this constraint
    // owns both ends of every cancellation.)
    _edge_lines.reserve(_edges.size());
    for (size_t i = 0; i < _edges.size(); ++i) {
        const auto & e = _edges[i];
        auto left = deview_operand(e.x, "left");
        auto right = deview_operand(e.y, "right");
        auto d = e.d - left.offset + right.offset;

        WPBSum sum;
        if (left.variable)
            sum += 1_i * IntegerVariableID{*left.variable};
        if (right.variable)
            sum += -1_i * IntegerVariableID{*right.variable};

        // An aliased edge leaves the same variable in the sum twice with
        // opposite coefficients, and a two-constant edge leaves the sum empty:
        // both render as a row whose left hand side is zero, which is exactly
        // what 0 <= d says, and which VeriPB reads as trivially true or
        // directly false according to d's sign.
        _edge_lines.push_back(model.add_labelled_constraint(constraint_id(), "e" + to_string(i), move(sum) <= d));
    }
}

auto DifferenceConstraints::install_propagators(Propagators & propagators) -> void
{
    if (_root_contradiction_posted_index) {
        // The edge's own OPB row is `0 >= something positive', so the
        // contradiction is RUP from the model with no state involved at all.
        propagators.install_initial_contradiction("difference constraint x - x <= d with d < 0", JustifyUsingRUP{}, NoReason{});
        return;
    }

    if (_graph_edges.empty() && _static_bounds.empty())
        return;

    Triggers triggers;
    for (const auto & v : _nodes)
        triggers.on_bounds.emplace_back(v);

    propagators.install(
        constraint_id(),
        [nodes = move(_nodes), graph_edges = move(_graph_edges), static_bounds = move(_static_bounds), edge_lines = move(_edge_lines)](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            auto n = nodes.size();
            auto m = graph_edges.size();

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
                                          PolBuilder pol;
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
            auto lb_tail_of = [](const GraphEdge & g) { return g.from; };
            auto lb_head_of = [](const GraphEdge & g) { return g.to; };

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
                                          PolBuilder pol;
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

            auto ub_tail_of = [](const GraphEdge & g) { return g.to; };
            auto ub_head_of = [](const GraphEdge & g) { return g.from; };

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
                                          PolBuilder pol;
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
            return PropagatorState::Enable;
        },
        triggers);
}

auto DifferenceConstraints::constraint_type() const -> string
{
    return "difference";
}

auto DifferenceConstraints::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();

    vector<SExpr> edges;
    for (const auto & e : _edges)
        edges.push_back(SExpr::list({tracker.s_expr_term_of(e.x), tracker.s_expr_term_of(e.y), SExpr::atom(e.d.to_string())}));

    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(move(edges))});
}
