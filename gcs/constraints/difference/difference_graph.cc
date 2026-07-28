#include <gcs/constraints/difference/difference_graph.hh>
#include <gcs/constraints/difference/difference_simplify.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>

#include <util/overloaded.hh>

#include <algorithm>
#include <chrono>
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
using std::chrono::duration;
using std::chrono::steady_clock;
using std::ranges::count;
using std::ranges::find;
using std::ranges::find_if;

namespace
{
    // The propagator's hot data: one of these per edge, scanned end to end once
    // per Bellman-Ford round, so its *size* is a measurable property rather than
    // a detail. Carrying the edge's optional<IntegerVariableCondition> inline
    // took DifferenceGraphEdge from 32 bytes to 96 and cost 2.9x on
    // examples/difference_chain at n = 640 --- 0.32 s to 0.93 s with the
    // propagation and recursion counts unchanged, i.e. pure memory traffic in
    // the innermost loop.
    //
    // So DifferenceGraphEdge stays the convenient *construction* type, with the
    // condition attached to the edge it belongs to, and install_difference_
    // propagator repacks it once: arcs here, conditions in a parallel array read
    // only when the active set is snapshotted (once per call) and when a reason
    // is built (only when something is inferred). Never inside a round.
    struct DifferenceArc
    {
        size_t from;
        size_t to;
        Integer d;
        size_t posted_index;
    };

    static_assert(sizeof(DifferenceArc) <= 32, "the difference-logic relaxation loop scans this array once per round; keep it small");

    // Publishes the simplification counters on the way out, whichever way out it
    // is.
    //
    // The stage can raise a contradiction in the middle of its own work, and
    // that is not an edge case: it is the *best* outcome it has. Fixing one
    // polarity of an ordering Boolean and then finding that the other polarity
    // is equally impossible is a root refutation, and the inference tracker
    // signals it by unwinding out of the propagator. Counters assigned at the
    // end of the block would be lost exactly on the runs that most need
    // explaining, so a destructor publishes them instead --- and times the stage
    // while it is there, since the paper is explicit that its one-off cubic cost
    // should be reported separately rather than folded into the solve.
    struct DifferenceSimplificationReporter
    {
        DifferenceSimplificationStats & stats;
        const std::shared_ptr<DifferenceSimplificationStats> & report_to;
        steady_clock::time_point started = steady_clock::now();

        ~DifferenceSimplificationReporter()
        {
            stats.seconds = duration<double>(steady_clock::now() - started).count();
            if (report_to)
                *report_to = stats;
        }
    };
}

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

auto gcs::innards::install_difference_propagator(
    Propagators & propagators, const ConstraintID & constraint_id, DifferenceGraph graph, DifferenceSimplificationOptions simplify) -> void
{
    if (graph.edges.empty() && graph.static_bounds.empty() && graph.disallowed_conditions.empty())
        return;

    Triggers triggers;
    for (const auto & v : graph.nodes)
        triggers.on_bounds.emplace_back(v);

    // A half-reified edge joins the graph the moment its condition becomes
    // true, so the propagator must wake on that as well as on the nodes'
    // bounds. `on_change' on the condition's variable is the coarsest trigger
    // gcs offers that is guaranteed to catch it: a condition can become true
    // through an interior removal (`x != v' the instant v leaves the domain),
    // which `on_bounds' does not see, and `on_instantiated' fires strictly less
    // often still (`x >= v' can become true long before x is fixed). Nothing
    // finer is needed, because there is no cheaper "becomes true" trigger and
    // the refined per-literal watches would have to be armed one per condition
    // anyway. Waking when a condition becomes *false* is not needed at all ---
    // an inactive edge simply does not participate, and no inference is lost by
    // finding that out later --- but `on_change' cannot distinguish the two
    // directions, and paying for the extra wake is cheaper than the machinery
    // to avoid it.
    //
    // Deliberately not deduplicated against the node list: a variable that is
    // both a graph node and somebody's condition would then have to give up one
    // of the two trigger kinds, and a duplicate wake is merely wasted work.
    {
        vector<IntegerVariableID> condition_vars;
        auto note = [&](const IntegerVariableCondition & c) {
            if (condition_vars.end() == find(condition_vars, c.var))
                condition_vars.push_back(c.var);
        };
        for (const auto & e : graph.edges)
            if (e.cond)
                note(*e.cond);
        for (const auto & sb : graph.static_bounds)
            if (sb.cond)
                note(*sb.cond);
        for (const auto & dc : graph.disallowed_conditions)
            note(dc.cond);
        for (const auto & v : condition_vars)
            triggers.on_change.emplace_back(v);
    }

    // Repack into the hot arc array plus a parallel condition array; see
    // DifferenceArc. The condition array stays *empty* when nothing is
    // conditional, which is both the check the propagator uses to take the
    // straight-through path and a guarantee that an unconditional system pays
    // nothing at all for this feature.
    vector<DifferenceArc> arcs;
    vector<optional<IntegerVariableCondition>> arc_conditions;
    arcs.reserve(graph.edges.size());
    for (const auto & e : graph.edges)
        arcs.push_back(DifferenceArc{e.from, e.to, e.d, e.posted_index});
    if (graph.edges.end() != find_if(graph.edges, [](const auto & e) { return e.cond.has_value(); })) {
        arc_conditions.reserve(graph.edges.size());
        for (const auto & e : graph.edges)
            arc_conditions.push_back(e.cond);
    }

    // Read before the capture list moves the node vector out from under it.
    auto number_of_nodes = graph.nodes.size();

    // The root simplification stage mutates `arcs`, `arc_conditions` and
    // `round_bound` in place, once, on the first call --- hence the `mutable`
    // below, which is the only mutable propagator state in this file. It is safe
    // without trailing for the same reason the paper's section 5.3 boundary is
    // where it is: the stage runs only at the root, before any decision, and
    // every conclusion it draws (this edge is implied by a path of unconditional
    // or root-fixed edges; this node has no edges left) is a statement about the
    // *graph*, which no amount of backtracking changes. Nothing here reads a
    // domain.
    propagators.install(
        constraint_id,
        [nodes = move(graph.nodes), arcs = move(arcs), arc_conditions = move(arc_conditions), static_bounds = move(graph.static_bounds),
            disallowed_conditions = move(graph.disallowed_conditions), edge_lines = move(graph.edge_lines), simplify = move(simplify),
            simplification_pending = true,
            round_bound = number_of_nodes](const State & state, auto & inference, ProofLogger * const logger) mutable -> PropagatorState {
            auto n = nodes.size();
            auto m = arcs.size();
            // arc_conditions is either empty --- nothing in this system is
            // conditional, and no per-edge storage exists at all --- or exactly
            // as long as arcs. Only the cold paths go through here; see
            // DifferenceArc for why the conditions are not in the arcs.
            auto condition_of = [&](size_t e) -> const optional<IntegerVariableCondition> & {
                static const optional<IntegerVariableCondition> none;
                return arc_conditions.empty() ? none : arc_conditions[e];
            };

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

            // A half-reified edge whose condition says `cond -> 0 <= d' with
            // d < 0 says `!cond', and saying so is a soundness obligation, not a
            // nicety: dropping the edge would licence solutions in which cond
            // holds and the constraint is violated. The row is `M.~cond >= -d'
            // with -d >= 1, which is the unit clause `~cond' after saturation,
            // so plain RUP against it suffices and nothing in the state is
            // involved. (Unconditionally this is a root contradiction instead;
            // see DifferenceConstraints::install_propagators.)
            for (const auto & dc : disallowed_conditions)
                if (LiteralIs::DefinitelyFalse != state.test_literal(dc.cond))
                    inference.infer(logger, ! dc.cond, JustifyUsingRUP{}, NoReason{});

            // Static bounds next: an edge with a constant operand is a plain
            // bound on the other operand, and once applied it is just part of
            // the state that Bellman-Ford seeds from. An unconditional one never
            // changes, so after the first call it is a no-op; a conditional one
            // applies from the moment its condition holds, and cites it.
            for (const auto & sb : static_bounds) {
                if (sb.cond && LiteralIs::DefinitelyTrue != state.test_literal(*sb.cond))
                    continue;
                Reason why = sb.cond ? Reason{ExplicitReason{ReasonLiterals{{*sb.cond}}}} : Reason{NoReason{}};
                if (sb.is_lower) {
                    if (state.lower_bound(nodes[sb.node]) < sb.value)
                        inference.infer_greater_than_or_equal(logger, nodes[sb.node], sb.value, JustifyUsingRUP{}, why);
                }
                else {
                    if (state.upper_bound(nodes[sb.node]) > sb.value)
                        inference.infer_less_than(logger, nodes[sb.node], sb.value + 1_i, JustifyUsingRUP{}, why);
                }
            }

            // The root simplification stage, which is the paper's Algorithm 4
            // (its section 5.2) run to the fixpoint of its section 5.3. Once, on
            // the first call, and only if that call is at the root --- which it
            // always is, since search begins by propagating everything before
            // any decision is made, but the guard is not decoration: everything
            // below is *permanent*, so doing it below a decision would keep
            // conclusions that only held under that decision, and no proof would
            // ever complain because losing propagation is invisible to a proof.
            //
            // Three of the paper's four sub-steps are here. Redundant-edge
            // removal and node removal are decisions about what to propagate,
            // not about what the model says --- the OPB keeps every posted row,
            // so there is nothing to certify. Fixing a condition false is a real
            // inference and carries the one proof obligation, discharged below.
            // Zero-weight-cycle unification is not implemented; the cycles are
            // counted so the question of whether it would pay is answerable from
            // a measurement (see dev_docs/difference-logic.md).
            if (simplification_pending) {
                simplification_pending = false;

                bool at_root = true;
                for ([[maybe_unused]] const auto & guess : state.guesses()) {
                    at_root = false;
                    break;
                }

                DifferenceSimplificationStats stats;
                DifferenceSimplificationReporter reporter{stats, simplify.stats};
                stats.nodes = n;
                stats.edges = m;
                for (size_t e = 0; e < m; ++e)
                    if (condition_of(e))
                        ++stats.conditional_edges;

                if (simplify.enabled && at_root && ! arcs.empty()) {
                    stats.ran = true;

                    vector<DifferenceSimplifyEdge> simplify_edges;
                    simplify_edges.reserve(m);
                    for (const auto & a : arcs)
                        simplify_edges.push_back(DifferenceSimplifyEdge{a.from, a.to, a.d});

                    vector<bool> dropped(m, false);
                    vector<DifferenceSimplifyRole> roles(m, DifferenceSimplifyRole::Base);

                    while (true) {
                        ++stats.rounds;

                        for (size_t e = 0; e < m; ++e) {
                            if (dropped[e])
                                roles[e] = DifferenceSimplifyRole::Ignored;
                            else if (const auto & cond = condition_of(e)) {
                                switch (state.test_literal(*cond)) {
                                    using enum LiteralIs;
                                case DefinitelyTrue: roles[e] = DifferenceSimplifyRole::Base; break;
                                case DefinitelyFalse:
                                    roles[e] = DifferenceSimplifyRole::Ignored;
                                    dropped[e] = true;
                                    ++stats.dead_edges_removed;
                                    break;
                                case Undecided: roles[e] = DifferenceSimplifyRole::Candidate; break;
                                }
                            }
                            else
                                roles[e] = DifferenceSimplifyRole::Base;
                        }

                        auto outcome = simplify_difference_graph(n, simplify_edges, roles);
                        if (outcome.base_negative_cycle) {
                            // The unconditional part of the system is already
                            // infeasible. Stop and let the Bellman-Ford pass
                            // below refute it: that is where the cycle
                            // extraction and the telescoping pol live, and
                            // duplicating them here would buy nothing.
                            stats.base_negative_cycle = true;
                            break;
                        }

                        stats.zero_weight_cycles = outcome.zero_weight_cycles;
                        stats.nodes_on_zero_weight_cycles = outcome.nodes_on_zero_weight_cycles;

                        for (size_t e = 0; e < m; ++e)
                            if (outcome.remove[e] && ! dropped[e]) {
                                dropped[e] = true;
                                ++stats.redundant_edges_removed;
                                if (condition_of(e))
                                    ++stats.redundant_conditional_edges_removed;
                            }

                        if (outcome.fix.empty())
                            break;

                        // Every round that gets here fixes at least one
                        // condition and so drops at least one edge, which is
                        // what bounds the loop --- an edge the pass wants to fix
                        // is never also an edge it wants to remove, since
                        // `d >= D_uv' and `d + D_vu < 0' cannot both hold when
                        // the graph has no negative cycle. That is an argument
                        // about the pass, though, and this is a loop inside a
                        // propagator, so make the progress explicit rather than
                        // inferred.
                        bool progress = false;

                        for (const auto & [candidate, path] : outcome.fix) {
                            if (dropped[candidate])
                                continue;

                            // Check the witness arithmetically before saying
                            // anything: that the candidate edge and the path
                            // really do form a cycle, and that it really does
                            // weigh less than zero. That is O(cycle), and it
                            // turns a bug in the shortest-path pass into an
                            // exception here rather than a VeriPB failure a
                            // hundred lines later (survey section 2.9.4).
                            auto weight = arcs[candidate].d;
                            auto at = arcs[candidate].to;
                            vector<IntegerVariableCondition> conditions;
                            for (auto e : path) {
                                if (arcs[e].from != at)
                                    throw UnexpectedException{"difference logic simplification built a disconnected witness cycle"};
                                weight += arcs[e].d;
                                at = arcs[e].to;
                                // A path edge may itself be conditional, on
                                // something currently definitely true --- either
                                // the model fixed it, or an earlier round of this
                                // very loop did. Its row then carries a big-M
                                // residual which does not telescope, so its
                                // condition has to be in the reason for the same
                                // reason a negative cycle's conditions are.
                                // Deduplicated, since one Boolean may appear on
                                // several edges.
                                if (const auto & cond = condition_of(e))
                                    if (conditions.end() == find(conditions, *cond))
                                        conditions.push_back(*cond);
                            }
                            if (at != arcs[candidate].from)
                                throw UnexpectedException{"difference logic simplification built a witness path that does not close"};
                            if (weight >= 0_i)
                                throw UnexpectedException{"difference logic simplification built a witness cycle of weight " + weight.to_string() +
                                    ", which is not negative"};

                            const auto & candidate_cond = condition_of(candidate);
                            if (! candidate_cond)
                                throw UnexpectedException{"difference logic simplification tried to fix the condition of an unconditional edge"};

                            // The proof is proof shape 1 with the candidate edge
                            // standing in for the missing link: sum the rows
                            // around the cycle and every BinEnc term telescopes
                            // away, leaving only the big-M residuals of the
                            // conditional edges. The candidate's is always one of
                            // them, so a saturate turns the sum into the clause
                            // `~cand v ~c_1 v ... v ~c_k' over the path's
                            // already-true conditions --- the reified_hand.pbp
                            // shape with the roles of the conditions swapped
                            // round. The closing RUP assumes the reason's
                            // literals and reads off `~cand'.
                            //
                            // Two mutation results, both measured rather than
                            // assumed, and both matching what the negative-cycle
                            // refutation already found:
                            //
                            //  * the `saturate' is not load-bearing --- removing
                            //    it leaves every fixture verifying, because the
                            //    closing RUP assumes every condition and drives
                            //    each residual to zero. Emitted anyway so the
                            //    derived line *is* the clause;
                            //  * neither, here, are the path's conditions in the
                            //    reason. That is specific to running at the root:
                            //    a path condition is definitely true only because
                            //    it is a *globally derived* fact (the model fixed
                            //    it, or an earlier round of this loop did), so
                            //    unit propagation recovers it and the RUP passes
                            //    without being told. They are cited regardless,
                            //    because the reason is also what the state and
                            //    the nogood machinery see, and there a missing
                            //    antecedent is not recoverable.
                            ReasonLiterals reason_literals;
                            for (const auto & c : conditions)
                                reason_literals.push_back(c);
                            auto reason = conditions.empty() ? Reason{NoReason{}} : Reason{ExplicitReason{move(reason_literals)}};
                            inference.infer(logger, ! *candidate_cond,
                                JustifyExplicitly{[&](const ReasonLiterals &) {
                                                      auto pol = edge_line_pol();
                                                      pol.add(edge_lines[arcs[candidate].posted_index]);
                                                      for (auto e : path)
                                                          pol.add(edge_lines[arcs[e].posted_index]);
                                                      pol.saturate();
                                                      pol.emit(*logger, ProofLevel::Temporary);
                                                  },
                                    ThenRUP::Yes},
                                reason);

                            dropped[candidate] = true;
                            progress = true;
                            ++stats.conditions_fixed;
                        }

                        if (! progress)
                            break;
                    }

                    // Now actually shrink the graph. Everything above only
                    // marked; this is where the propagator stops paying for what
                    // it marked.
                    if (dropped.end() != find(dropped, true)) {
                        vector<DifferenceArc> kept_arcs;
                        vector<optional<IntegerVariableCondition>> kept_conditions;
                        for (size_t e = 0; e < m; ++e)
                            if (! dropped[e]) {
                                kept_arcs.push_back(arcs[e]);
                                if (! arc_conditions.empty())
                                    kept_conditions.push_back(arc_conditions[e]);
                            }
                        arcs = move(kept_arcs);
                        // If nothing conditional survived, drop the parallel
                        // array entirely: an empty one is what puts the
                        // relaxation loop back on its straight-through path,
                        // which is worth 45% on examples/difference_chain.
                        if (kept_conditions.end() == find_if(kept_conditions, [](const auto & c) { return c.has_value(); }))
                            kept_conditions.clear();
                        arc_conditions = move(kept_conditions);
                        m = arcs.size();
                    }

                    // Node removal, the paper's last sub-step, and internal in
                    // exactly the same way: a node with no incident edge left
                    // cannot send or receive a bound, so it neither needs seeding
                    // nor counts towards the number of relaxation rounds a
                    // simple path can need.
                    vector<bool> live(n, false);
                    for (const auto & a : arcs) {
                        live[a.from] = true;
                        live[a.to] = true;
                    }
                    auto live_count = static_cast<size_t>(count(live, true));
                    stats.isolated_nodes_removed = n - live_count;
                    round_bound = live_count;
                }
            }

            // Which edges are in the graph *for this call*. A half-reified edge
            // participates exactly while its condition currently holds; the
            // paper's E' set, restricted to the entailed half, since nothing
            // here infers a condition from the graph.
            //
            // Snapshotting once, rather than re-testing as we go, is what keeps
            // the round bound and the cycle-extraction argument in
            // dev_docs/difference-logic.md applicable verbatim: both are
            // statements about one Bellman-Ford run over one fixed edge set, and
            // the edge set is now fixed for the duration of the call rather than
            // for the lifetime of the constraint. Nothing else in those
            // arguments mentions where the edges came from.
            //
            // The snapshot also stays *correct* as inferences land during the
            // call, which is why it is safe to cite a snapshotted condition in a
            // reason later on. A literal that is definitely true holds for every
            // value in the current domain, so it holds for every value in any
            // subset of it; all this propagator does is shrink domains, and a
            // domain shrunk to empty is a contradiction, which stops the call.
            // So a condition true at snapshot time is still true at every
            // inference made from it.
            //
            // An unconditional system is not snapshotted at all, and iterates
            // the arc array straight through. That is not fastidiousness: the
            // snapshot is a level of indirection inside the innermost loop, and
            // going through it unconditionally cost 45% on
            // examples/difference_chain at n = 640 (0.32 s to 0.47 s) with the
            // propagation count unchanged. The branch is on the *outside* of the
            // per-edge loop, so the conditional case pays nothing for it either.
            vector<size_t> active_edges;
            auto all_active = arc_conditions.empty();
            if (! all_active) {
                active_edges.reserve(m);
                for (size_t e = 0; e < m; ++e)
                    if (! arc_conditions[e] || LiteralIs::DefinitelyTrue == state.test_literal(*arc_conditions[e]))
                        active_edges.push_back(e);
            }

            auto for_each_active_edge = [&](auto && relax) {
                if (all_active)
                    for (size_t e = 0; e < m; ++e)
                        relax(e);
                else
                    for (auto e : active_edges)
                        relax(e);
            };

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
            // A half-reified edge on the cycle contributes one extra term,
            // `M.~cond', which does not telescope. Summing leaves
            // `sum_i M_i.~cond_i >= -(cycle weight)', and one saturate turns it
            // into the clause `~cond_1 v ... v ~cond_k' --- the learned clause,
            // and exactly the shape hand-verified against real gcs OPB output in
            // reified_hand.pbp before any of this was written. Every such
            // condition therefore has to appear in the reason: the refutation is
            // conditional on precisely them, and citing fewer would claim a
            // contradiction the model does not entail. *That* part is
            // load-bearing --- omitting a condition from the reason fails VeriPB
            // on the reified fixtures, confirmed by mutation.
            //
            // The saturate itself is not: the closing RUP assumes every
            // condition, which drives each `M.~cond' to zero and falsifies the
            // unsaturated line just as well, and removing the saturate leaves
            // every reified fixture verifying (also confirmed by mutation). It
            // is emitted anyway because it makes the derived line *be* the
            // clause rather than a big-M encoding of it, which is what a reader,
            // an assertion hint or a longer-lived proof level would want. It is
            // emitted only when there is a residual to saturate, so an
            // unconditional cycle's proof line is byte-for-byte what it was
            // before half-reified edges existed.
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
                vector<IntegerVariableCondition> conditions;
                for (size_t k = 0; k < cycle.size(); ++k) {
                    const auto & here = arcs[cycle[k]];
                    const auto & next = arcs[cycle[(k + 1) % cycle.size()]];
                    weight += here.d;
                    if (head_of(next) != tail_of(here))
                        throw UnexpectedException{"difference logic extracted a disconnected negative cycle"};
                    // Deduplicated, because the same Boolean legitimately
                    // appears on more than one edge (a disjunctive encoding
                    // makes that the normal case) and a reason listing it twice
                    // would render a proof line with a repeated literal.
                    const auto & here_cond = condition_of(cycle[k]);
                    if (here_cond && conditions.end() == find(conditions, *here_cond))
                        conditions.push_back(*here_cond);
                }
                if (weight >= 0_i)
                    throw UnexpectedException{"difference logic extracted a cycle of weight " + weight.to_string() + ", which is not negative"};

                auto conditional = ! conditions.empty();
                ReasonLiterals reason_literals;
                for (const auto & c : conditions)
                    reason_literals.push_back(c);

                inference.contradiction(logger,
                    JustifyExplicitly{[&](const ReasonLiterals &) {
                                          auto pol = edge_line_pol();
                                          for (auto e : cycle)
                                              pol.add(edge_lines[arcs[e].posted_index]);
                                          if (conditional)
                                              pol.saturate();
                                          pol.emit(*logger, ProofLevel::Temporary);
                                      },
                        ThenRUP::Yes},
                    conditional ? Reason{ExplicitReason{move(reason_literals)}} : Reason{NoReason{}});
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
                    at = tail_of(arcs[*pred[at]]);
                }

                vector<size_t> cycle;
                auto here = at;
                do {
                    cycle.push_back(*pred[here]);
                    here = tail_of(arcs[*pred[here]]);
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
                        at = tail_of(arcs[*pred[at]]);
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
            auto lb_tail_of = [](const DifferenceArc & g) { return g.from; };
            auto lb_head_of = [](const DifferenceArc & g) { return g.to; };

            for (size_t round = 0; round <= round_bound; ++round) {
                bool changed = false;
                for_each_active_edge([&](size_t e) {
                    const auto & edge = arcs[e];
                    auto candidate = lb[edge.from] - edge.d;
                    if (candidate > lb[edge.to]) {
                        lb[edge.to] = candidate;
                        lb_pred[edge.to] = e;
                        changed = true;
                        if (round == round_bound)
                            contradict_on_cycle(extract_cycle(edge.to, lb_pred, lb_tail_of), lb_tail_of, lb_head_of);
                    }
                });
                if (! changed)
                    break;
            }

            infer_along_forest(lb_pred, lb_tail_of, [&](size_t v) {
                const auto & edge = arcs[*lb_pred[v]];
                const auto & edge_cond = condition_of(*lb_pred[v]);
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
                //
                // A half-reified edge adds `M.~cond' to that sum, and its
                // condition to the reason. Only *this* edge's condition, because
                // the inference is per edge: the predecessor's bound was either
                // already there when the call started, or was itself inferred a
                // moment ago carrying its own edge's condition in its own
                // reason, so the conditions along a whole path are cited by the
                // chain of inferences rather than by any one of them. Each link
                // is a standalone entailment of one row, which is what makes its
                // RUP check.
                //
                // No saturate here, unlike the cycle refutation: the residual is
                // harmless under the closing RUP, which assumes cond and so
                // drives that term to zero, leaving the line the unconditional
                // case would have produced. Saturating would instead clamp
                // BinEnc(v)'s own coefficients against the degree, for no gain.
                inference.infer_greater_than_or_equal(logger, nodes[v], lb[v],
                    JustifyExplicitly{[&](const ReasonLiterals &) {
                                          auto pol = edge_line_pol();
                                          pol.add(edge_lines[edge.posted_index]);
                                          pol.add_for_literal(logger->names_and_ids_tracker(), source >= source_lb);
                                          pol.emit(*logger, ProofLevel::Temporary);
                                      },
                        ThenRUP::Yes},
                    ExplicitReason{edge_cond ? ReasonLiterals{{source >= source_lb}, {*edge_cond}} : ReasonLiterals{{source >= source_lb}}});
            });

            // Upper bounds flow backwards along the same edges. Edge
            // x --d--> y is also x <= y + d, so ub(x) <= ub(y) + d: shortest
            // paths in the reverse graph, seeded from the current upper bounds.
            vector<Integer> ub(n, 0_i);
            vector<optional<size_t>> ub_pred(n, nullopt);
            for (size_t v = 0; v < n; ++v)
                ub[v] = state.upper_bound(nodes[v]);

            auto ub_tail_of = [](const DifferenceArc & g) { return g.to; };
            auto ub_head_of = [](const DifferenceArc & g) { return g.from; };

            for (size_t round = 0; round <= round_bound; ++round) {
                bool changed = false;
                for_each_active_edge([&](size_t e) {
                    const auto & edge = arcs[e];
                    auto candidate = ub[edge.to] + edge.d;
                    if (candidate < ub[edge.from]) {
                        ub[edge.from] = candidate;
                        ub_pred[edge.from] = e;
                        changed = true;
                        if (round == round_bound)
                            contradict_on_cycle(extract_cycle(edge.from, ub_pred, ub_tail_of), ub_tail_of, ub_head_of);
                    }
                });
                if (! changed)
                    break;
            }

            infer_along_forest(ub_pred, ub_tail_of, [&](size_t v) {
                const auto & edge = arcs[*ub_pred[v]];
                const auto & edge_cond = condition_of(*ub_pred[v]);
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
                    ExplicitReason{
                        edge_cond ? ReasonLiterals{{source < source_ub + 1_i}, {*edge_cond}} : ReasonLiterals{{source < source_ub + 1_i}}});
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
