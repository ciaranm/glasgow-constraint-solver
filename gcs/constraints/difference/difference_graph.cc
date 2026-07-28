#include <gcs/constraints/difference/difference_graph.hh>
#include <gcs/constraints/difference/difference_incremental.hh>
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
#include <any>
#include <chrono>
#include <cstdlib>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::any_cast;
using std::move;
using std::nullopt;
using std::optional;
using std::size_t;
using std::string;
using std::vector;
using std::chrono::duration;
using std::chrono::steady_clock;
using std::ranges::count;
using std::ranges::find;
using std::ranges::find_if;

namespace
{
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

    // What one undo record restores. The potential function is deliberately not
    // in here: it is never trailed, because its invariant is a conjunction over
    // the edges currently in the graph and backtracking only ever removes edges.
    enum class DifferenceTrailKind
    {
        LowerGate,
        UpperGate,
        Activation
    };

    // For a gate entry, `value` is the bound to restore; for an activation
    // entry, it is the record's previous setting, which is not always zero ---
    // the defensive path that drops a record for an arc that has gone inactive
    // has to be undone the other way round.
    struct DifferenceTrailEntry
    {
        DifferenceTrailKind kind;
        size_t index;
        Integer value;
    };

    // Everything the incremental propagator remembers between calls.
    //
    // None of it is copied by the engine: the one thing that *is* trailed is a
    // single number, the length of `trail` that belongs to the current epoch, so
    // an epoch costs O(1) to enter rather than O(n + m) to copy. Unwinding
    // `trail` down to that mark restores `do_lb`, `do_ub` and `arc_was_active`
    // to *exactly* the values they had at the restore point.
    //
    // Exactness is the whole point. The tempting cheap alternative --- clamp
    // `Do` against the current bounds at the next call instead of restoring it
    // --- is wrong, and silently so. Guess `y >= 10`; the propagator runs and
    // records `Do(y) = 10`; the branch fails; `y >= 5` is restored; the sibling
    // guesses `y >= 7`. The clamp gives `Do(y) = min(10, 7) = 7`, which is
    // `min D(y)`, so `y` is not in `Vl`, the gate never expands, and the
    // consequences of `y >= 7` --- which were computed in a branch that has been
    // thrown away --- are lost. Successive guesses tightening the same variable
    // is the single most common branching pattern there is, and no proof can see
    // the loss.
    struct DifferencePropagatorMemory
    {
        // Dijkstra needs adjacency where Bellman-Ford needed only a flat scan.
        // Built once over every arc; the currently active ones are selected by
        // `active_flags` during traversal.
        DifferenceAdjacency by_tail, by_head;

        // Valid for every currently active arc, monotonically decreasing over
        // the whole search, never reset and never trailed. `neg_potential` is
        // maintained alongside it rather than rebuilt per call, for the same
        // reason as `do_ub_neg`: it is the upper bound pass's potential.
        vector<Integer> potential, neg_potential;

        // The paper's Do: the bounds the previous run propagated *from*. The
        // upper half is stored negated, because that is the form the shared
        // implementation of IncLB reads it in and negating it per call was
        // measurable on `examples/rcpsp_max`.
        vector<Integer> do_lb, do_ub_neg;

        // Which arcs the incremental machinery has established its invariants
        // for. Empty when the system is unconditional, in which case every arc
        // is active for ever and there is nothing to track.
        vector<char> arc_was_active;

        vector<DifferenceTrailEntry> trail;

        // Per-call scratch, hoisted so that a wake allocates nothing.
        // `ub_start_neg` is the sign-flipped copy of the current upper bounds,
        // which is what lets one implementation of IncLB serve both directions.
        // `pass_bound` and `pass_pred` belong to the from-scratch route and to
        // the audit's re-run of it.
        vector<size_t> active_edges, changed_arcs;
        vector<char> active_flags;
        vector<char> forced_lb, forced_ub;
        vector<Integer> lb_start, ub_start_neg;
        vector<Integer> pass_bound, claim;
        vector<optional<size_t>> pass_pred;

        DifferencePotentialWorkspace potential_work;
        DifferenceBoundsWorkspace bounds_work;
    };

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
    //
    // Lifted out of the propagator rather than left inline: MSVC's optimiser
    // gives up with an internal compiler error on a function the size the
    // propagator had reached, and a 230-line block inside a 700-line lambda was
    // not doing a reader any favours either.
    template <typename Inference_>
    auto run_difference_root_simplification(const State & state, Inference_ & inference, ProofLogger * const logger, size_t number_of_nodes,
        vector<DifferenceArc> & arcs, vector<optional<IntegerVariableCondition>> & arc_conditions, const vector<ProofLine> & edge_lines,
        const DifferenceSimplificationOptions & simplify, size_t & round_bound, bool at_root) -> void
    {
        auto n = number_of_nodes;
        auto m = arcs.size();

        auto condition_of = [&](size_t e) -> const optional<IntegerVariableCondition> & {
            static const optional<IntegerVariableCondition> none;
            return arc_conditions.empty() ? none : arc_conditions[e];
        };

        auto edge_line_pol = [&]() {
            PolBuilder pol;
            pol.enable_deview_mode(logger->names_and_ids_tracker());
            return pol;
        };

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
                    // infeasible. Stop and let the from-scratch pass
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
                        throw UnexpectedException{
                            "difference logic simplification built a witness cycle of weight " + weight.to_string() + ", which is not negative"};

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

    // One call of the propagator, with the context every part of it needs.
    //
    // A struct rather than one very long lambda for a blunt reason: the lambda
    // reached a size at which MSVC's front end gives up with an internal
    // compiler error (`msc1.cpp`, line 1589), and it was well past readable
    // before that. Splitting it changes nothing about what runs --- the members
    // below are the same code with the same names, in the same order.
    //
    // The reference members are what the lambda's `[&]` capture was, so the
    // bodies are unchanged; `const` on the members refers to the references and
    // not to what they refer to, which is why a member that mutates `memory` or
    // infers through `inference` is still const.
    template <typename Inference_>
    struct DifferenceCall
    {
        const State & state;
        Inference_ & inference;
        ProofLogger * const logger;
        const vector<SimpleIntegerVariableID> & nodes;
        const vector<DifferenceArc> & arcs;
        const vector<optional<IntegerVariableCondition>> & arc_conditions;
        const vector<ProofLine> & edge_lines;
        const DifferenceIncrementalOptions & incremental;
        DifferencePropagatorMemory & memory;
        ConstraintStateHandle trail_mark_handle;
        size_t n;
        size_t m;
        size_t round_bound;
        bool all_active;

        // arc_conditions is either empty --- nothing in this system is
        // conditional, and no per-edge storage exists at all --- or exactly as
        // long as arcs. Only the cold paths go through here; see DifferenceArc
        // for why the conditions are not in the arcs.
        auto condition_of(size_t e) const -> const optional<IntegerVariableCondition> &
        {
            static const optional<IntegerVariableCondition> none;
            return arc_conditions.empty() ? none : arc_conditions[e];
        }

        // Every pol below cites an edge row in deview mode. For rows this
        // constraint emitted itself that is a no-op: they are already over bare
        // variables, so no deview-form is registered for them and
        // deviewed_line_for hands the line straight back. It matters for a
        // presolver-built graph, whose rows belong to somebody else's constraint
        // and are therefore in the user's views' bits, while the arithmetic here
        // (and the reason literals) is over the canonical bare variables. Same
        // reasoning, and the same fix, as linear/justify.cc.
        auto edge_line_pol() const -> PolBuilder
        {
            PolBuilder pol;
            pol.enable_deview_mode(logger->names_and_ids_tracker());
            return pol;
        }

        auto for_each_active_edge(auto && relax) const -> void
        {
            if (all_active)
                for (size_t e = 0; e < m; ++e)
                    relax(e);
            else
                for (auto e : memory.active_edges)
                    relax(e);
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
        auto contradict_on_cycle(const vector<size_t> & cycle, auto && tail_of, auto && head_of) const -> void
        {
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
        }

        // Walk predecessors back from `start' looking for a cycle, which is
        // total: the walk cannot run off the end of the predecessor forest,
        // and whatever cycle it does reach is a negative one. Both are
        // proved in dev_docs/difference-logic.md ("Rounds, and why the
        // extraction is total"); in outline, a walk that reached a
        // predecessor-less node would exhibit a real path into `start'
        // whose source has held its seeded distance since before round 0,
        // and the round bound below says that path has already propagated,
        // contradicting the strict improvement that just happened.
        auto extract_cycle(size_t start, const vector<optional<size_t>> & pred, auto && tail_of) const -> vector<size_t>
        {
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
        }

        // Infer improved bounds in an order consistent with the predecessor
        // forest, so that each node's push cites its predecessor's bound
        // *after* that bound has been applied. Roots of the forest are the
        // nodes whose bound did not improve, so every node with a
        // predecessor gets exactly one inference.
        auto infer_along_forest(const vector<optional<size_t>> & pred, auto && tail_of, auto && infer_one) const -> void
        {
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
        }

        // One edge, one pol: the edge row plus the definition row of the
        // predecessor's bound literal cancels BinEnc(source) and leaves
        // BinEnc(v) >= source_bound - d, which is exactly what the closing
        // RUP needs. This is justify_linear_bounds for a two-term linear,
        // and it is the shape verified by hand in boundpush_hand.pbp.
        // Citing the predecessor's own bound is already the paper's
        // "lifted" explanation: the weakest antecedent for v >= L - d
        // across this edge *is* source >= L, so the pol's degree comes out
        // at exactly the pushed amount with no wasted slack.
        //
        // A half-reified edge adds `M.~cond' to that sum, and its condition
        // to the reason. Only *this* edge's condition, because the
        // inference is per edge: the predecessor's bound was either already
        // there when the call started, or was itself inferred a moment ago
        // carrying its own edge's condition in its own reason, so the
        // conditions along a whole path are cited by the chain of
        // inferences rather than by any one of them. Each link is a
        // standalone entailment of one row, which is what makes its RUP
        // check.
        //
        // No saturate here, unlike the cycle refutation: the residual is
        // harmless under the closing RUP, which assumes cond and so drives
        // that term to zero, leaving the line the unconditional case would
        // have produced. Saturating would instead clamp BinEnc(v)'s own
        // coefficients against the degree, for no gain.
        //
        // Shared between the from-scratch and the incremental passes, so
        // that the two cannot drift apart in what they emit. The self-checks
        // are what turn a predecessor-walk or a settle-order bug into an
        // exception here rather than a VeriPB failure much later.
        auto infer_lower_bound(size_t v, Integer new_bound, size_t arc_index, Integer source_bound) const -> void
        {
            const auto & edge = arcs[arc_index];
            const auto & edge_cond = condition_of(arc_index);
            if (edge.to != v)
                throw UnexpectedException{"difference logic lower bound was pushed along an edge that does not end at it"};
            if (source_bound - edge.d != new_bound)
                throw UnexpectedException{"difference logic lower bound does not match its predecessor edge"};
            if (state.lower_bound(nodes[v]) >= new_bound)
                return;

            auto source = nodes[edge.from];
            inference.infer_greater_than_or_equal(logger, nodes[v], new_bound,
                JustifyExplicitly{[&](const ReasonLiterals &) {
                                      auto pol = edge_line_pol();
                                      pol.add(edge_lines[edge.posted_index]);
                                      pol.add_for_literal(logger->names_and_ids_tracker(), source >= source_bound);
                                      pol.emit(*logger, ProofLevel::Temporary);
                                  },
                    ThenRUP::Yes},
                ExplicitReason{edge_cond ? ReasonLiterals{{source >= source_bound}, {*edge_cond}} : ReasonLiterals{{source >= source_bound}}});
        }

        auto infer_upper_bound(size_t v, Integer new_bound, size_t arc_index, Integer source_bound) const -> void
        {
            const auto & edge = arcs[arc_index];
            const auto & edge_cond = condition_of(arc_index);
            if (edge.from != v)
                throw UnexpectedException{"difference logic upper bound was pushed along an edge that does not start at it"};
            if (source_bound + edge.d != new_bound)
                throw UnexpectedException{"difference logic upper bound does not match its predecessor edge"};
            if (state.upper_bound(nodes[v]) <= new_bound)
                return;

            auto source = nodes[edge.to];
            inference.infer_less_than(logger, nodes[v], new_bound + 1_i,
                JustifyExplicitly{[&](const ReasonLiterals &) {
                                      auto pol = edge_line_pol();
                                      pol.add(edge_lines[edge.posted_index]);
                                      pol.add_for_literal(logger->names_and_ids_tracker(), source < source_bound + 1_i);
                                      pol.emit(*logger, ProofLevel::Temporary);
                                  },
                    ThenRUP::Yes},
                ExplicitReason{
                    edge_cond ? ReasonLiterals{{source < source_bound + 1_i}, {*edge_cond}} : ReasonLiterals{{source < source_bound + 1_i}}});
        }

        // Lower bounds flow forwards. Edge x --d--> y is x - y <= d, i.e.
        // y >= x - d, so lb(y) >= lb(x) - d. Writing dist(v) = -lb(v) this
        // is single-source shortest paths from the paper's dummy vertex v0,
        // whose edge to v weighs -lb(v): that is exactly how the seeding
        // below encodes the current bounds (Corollary 1). Upper bounds flow
        // backwards along the same edges: x --d--> y is also x <= y + d, so
        // ub(x) <= ub(y) + d, which is shortest paths in the reverse graph.
        static auto lb_tail_of(const DifferenceArc & g) -> size_t
        {
            return g.from;
        }
        static auto lb_head_of(const DifferenceArc & g) -> size_t
        {
            return g.to;
        }
        static auto ub_tail_of(const DifferenceArc & g) -> size_t
        {
            return g.to;
        }
        static auto ub_head_of(const DifferenceArc & g) -> size_t
        {
            return g.from;
        }

        // The from-scratch Bellman-Ford relaxation, to the fixpoint of the
        // bounds abstraction.
        //
        // A shortest path from v0 is simple, so after the seeding (which is
        // the v0 edge set) it uses at most n - 1 real edges, and n - 1
        // relaxation rounds suffice. Rounds 0 .. round_bound give one more
        // than needed; a relaxation that still succeeds in the last round is
        // sound evidence that the system has a negative cycle, and the
        // extraction above is then guaranteed to find it.
        //
        // With `refute` set this refutes on the spot, at the exact edge that
        // relaxed, which is what the shipping non-incremental path wants.
        // Without it the cycle is only reported, which is what the audit
        // wants: it needs to know whether the incremental pass missed one,
        // not to duplicate the refutation.
        auto relax_lower_bounds(vector<Integer> & lb, vector<optional<size_t>> & lb_pred, bool refute) const -> bool
        {
            for (size_t round = 0; round <= round_bound; ++round) {
                bool changed = false, cycle = false;
                for_each_active_edge([&](size_t e) {
                    if (cycle)
                        return;
                    const auto & edge = arcs[e];
                    auto candidate = lb[edge.from] - edge.d;
                    if (candidate > lb[edge.to]) {
                        lb[edge.to] = candidate;
                        lb_pred[edge.to] = e;
                        changed = true;
                        if (round == round_bound) {
                            if (refute)
                                contradict_on_cycle(extract_cycle(edge.to, lb_pred, lb_tail_of), lb_tail_of, lb_head_of);
                            cycle = true;
                        }
                    }
                });
                if (cycle)
                    return true;
                if (! changed)
                    break;
            }
            return false;
        }

        auto relax_upper_bounds(vector<Integer> & ub, vector<optional<size_t>> & ub_pred, bool refute) const -> bool
        {
            for (size_t round = 0; round <= round_bound; ++round) {
                bool changed = false, cycle = false;
                for_each_active_edge([&](size_t e) {
                    if (cycle)
                        return;
                    const auto & edge = arcs[e];
                    auto candidate = ub[edge.to] + edge.d;
                    if (candidate < ub[edge.from]) {
                        ub[edge.from] = candidate;
                        ub_pred[edge.from] = e;
                        changed = true;
                        if (round == round_bound) {
                            if (refute)
                                contradict_on_cycle(extract_cycle(edge.from, ub_pred, ub_tail_of), ub_tail_of, ub_head_of);
                            cycle = true;
                        }
                    }
                });
                if (cycle)
                    return true;
                if (! changed)
                    break;
            }
            return false;
        }

        // A negative cycle found by IncSat, or by the initial potential
        // computation, is refuted by handing straight over to the
        // from-scratch pass, which already carries the extraction and the
        // telescoping pol. A negative cycle ends the search, so the O(n.m)
        // is paid at most once per branch and buys a second implementation
        // that does not have to be written or trusted.
        auto refute_negative_cycle(const char * who) const -> void
        {
            memory.pass_bound.assign(n, 0_i);
            memory.pass_pred.assign(n, nullopt);
            for (size_t v = 0; v < n; ++v)
                memory.pass_bound[v] = state.lower_bound(nodes[v]);
            static_cast<void>(relax_lower_bounds(memory.pass_bound, memory.pass_pred, true));
            throw UnexpectedException{string{"difference logic "} + who +
                " reported a negative cycle that the from-scratch pass could not find, so one of the two is wrong"};
        }

        // The from-scratch route: one Bellman-Ford pass each way from the
        // current bounds, every wake. Kept compiled and selectable because it is
        // the reference the incremental route is checked against --- `recursions`
        // and the solution sequence must come out identical, and a lost
        // inference is invisible to VeriPB.
        auto run_from_scratch() const -> void
        {
            // The from-scratch route: one Bellman-Ford pass each way from
            // the current bounds, every wake. Kept compiled and selectable
            // because it is the reference the incremental route is checked
            // against --- `recursions` and the solution sequence must come
            // out identical, and a lost inference is invisible to VeriPB.
            auto & lb = memory.pass_bound;
            auto & lb_pred = memory.pass_pred;
            lb.assign(n, 0_i);
            lb_pred.assign(n, nullopt);
            for (size_t v = 0; v < n; ++v)
                lb[v] = state.lower_bound(nodes[v]);
            static_cast<void>(relax_lower_bounds(lb, lb_pred, true));
            infer_along_forest(lb_pred, lb_tail_of, [&](size_t v) { infer_lower_bound(v, lb[v], *lb_pred[v], lb[arcs[*lb_pred[v]].from]); });

            auto & ub = memory.pass_bound;
            auto & ub_pred = memory.pass_pred;
            ub.assign(n, 0_i);
            ub_pred.assign(n, nullopt);
            for (size_t v = 0; v < n; ++v)
                ub[v] = state.upper_bound(nodes[v]);
            static_cast<void>(relax_upper_bounds(ub, ub_pred, true));
            infer_along_forest(ub_pred, ub_tail_of, [&](size_t v) { infer_upper_bound(v, ub[v], *ub_pred[v], ub[arcs[*ub_pred[v]].to]); });
        }

        auto run_incremental(bool first_call, bool at_root) const -> void
        {
            if (first_call) {
                if (! at_root)
                    throw UnexpectedException{"difference logic incremental state was initialised below a decision, where nothing it concludes "
                                              "would survive backtracking"};

                memory.by_tail = build_difference_adjacency(n, arcs, true);
                memory.by_head = build_difference_adjacency(n, arcs, false);
                memory.do_lb.assign(n, 0_i);
                memory.do_ub_neg.assign(n, 0_i);
                memory.forced_lb.assign(n, 0);
                memory.forced_ub.assign(n, 0);
                memory.lb_start.assign(n, 0_i);
                memory.ub_start_neg.assign(n, 0_i);
                if (! all_active)
                    memory.arc_was_active = memory.active_flags;

                // One Bellman-Ford, once, for the potential function. Every
                // later change to the active arc set goes through IncSat
                // instead, which is what makes a wake O(n log n + m) rather
                // than O(n.m). No trail entries: this is the root, and the
                // trail mark stays where it is.
                auto initial_potential = difference_initial_potential(n, arcs, memory.active_flags);
                if (! initial_potential)
                    refute_negative_cycle("the initial potential computation");
                memory.potential = move(*initial_potential);
                memory.neg_potential.assign(n, 0_i);
                for (size_t v = 0; v < n; ++v)
                    memory.neg_potential[v] = -memory.potential[v];
            }

            memory.forced_lb.assign(n, 0);
            memory.forced_ub.assign(n, 0);

            if (first_call) {
                // Nothing has been propagated from anything yet, so every node
                // has to be seeded and expanded once. Setting Do to the current
                // bounds and forcing every node is exactly that, and it leaves
                // both gate invariants established when the pass finishes.
                for (size_t v = 0; v < n; ++v) {
                    memory.forced_lb[v] = 1;
                    memory.forced_ub[v] = 1;
                }
            }
            else if (! memory.changed_arcs.empty()) {
                // Arcs whose activity has changed since the last run. Each
                // newly active one needs *both* halves of the paper's section
                // 4.4 treatment, and its section 5.4's during-search description
                // gives only the first: repair the potential function (or find
                // that the arc closes a negative cycle), *and* seed bound
                // propagation across it. Without the second, a condition becoming true with no node
                // bound changing anywhere leaves Vl empty and the push the arc
                // delivers is silently lost.
                //
                // Seeding is done by forcing the arc's tail into Vl for the
                // lower bound pass and its head for the upper bound pass, rather
                // than by touching Do: Dijkstra then carries that node's bound
                // across the new arc and on downstream, and the Do update at the
                // end re-establishes I2 for the arc as a side effect.
                //
                // Re-activation after backtracking counts, every time. The
                // potential function is never reset and drifts downwards over
                // the whole search, so an arc that was valid when it was last
                // active may need repair now; nothing may cache "this arc has
                // been checked".
                bool potential_moved = false;
                for (auto e : memory.changed_arcs) {
                    if (0 != memory.active_flags[e]) {
                        memory.trail.push_back(DifferenceTrailEntry{DifferenceTrailKind::Activation, e, 0_i});
                        memory.arc_was_active[e] = 1;

                        // IncSat over `arc_was_active`, not over the current
                        // active set: the potential is valid for exactly the
                        // arcs recorded there, and the loop adds this one to it
                        // just before repairing, so each new arc is handled
                        // against a graph the potential is already valid for.
                        if (! difference_repair_potential(n, arcs, memory.by_tail, memory.arc_was_active, memory.potential, e, memory.potential_work))
                            refute_negative_cycle("IncSat");
                        potential_moved = true;
                        memory.forced_lb[arcs[e].from] = 1;
                        memory.forced_ub[arcs[e].to] = 1;
                    }
                    else {
                        // An arc that was active at the restore point but is not
                        // now. Going down a branch this cannot happen --- a
                        // definitely-true literal stays definitely true as
                        // domains shrink --- so this is defensive. Dropping the
                        // record is always safe: an inactive arc has no
                        // invariant to maintain, and it will be treated as new
                        // if it ever comes back.
                        memory.trail.push_back(DifferenceTrailEntry{DifferenceTrailKind::Activation, e, 1_i});
                        memory.arc_was_active[e] = 0;
                    }
                }

                if (potential_moved)
                    for (size_t v = 0; v < n; ++v)
                        memory.neg_potential[v] = -memory.potential[v];
            }

            if (incremental.audit)
                if (auto bad = difference_invalid_potential_arc(arcs, memory.active_flags, memory.potential))
                    throw UnexpectedException{"difference logic entered a call with an invalid potential function, at arc " + std::to_string(*bad)};

            // Both bounds of every node, in one pass. Reading the upper bounds
            // now rather than after the lower bound pass is not a shortcut: a
            // lower bound inference removes values *below* a bound and so cannot
            // move an upper bound at all (a domain it emptied would have raised
            // a contradiction and ended the call), so the values are the same
            // either way. It matters because the two accessors were the single
            // largest line in the profile of a wake.
            for (size_t v = 0; v < n; ++v) {
                auto [l, u] = state.bounds(nodes[v]);
                memory.lb_start[v] = l;
                memory.ub_start_neg[v] = -u;
            }

            // IncLB. `Vl`, `pi(v0)` and the seeds are all computed inside; the
            // settle order that comes back is the order the pushes have to be
            // made in, so that each cites the one before it.
            if (first_call) {
                memory.do_lb = memory.lb_start;
                memory.do_ub_neg = memory.ub_start_neg;
            }

            difference_incremental_bounds(n, arcs, memory.by_tail, true, memory.active_flags, memory.potential, memory.lb_start, memory.do_lb,
                memory.forced_lb, memory.bounds_work);

            for (auto v : memory.bounds_work.settle_order)
                if (memory.bounds_work.has_predecessor[v] && memory.bounds_work.settled_bound[v] > memory.lb_start[v]) {
                    auto e = memory.bounds_work.predecessor[v];
                    infer_lower_bound(v, memory.bounds_work.settled_bound[v], e, memory.bounds_work.settled_bound[arcs[e].from]);
                }

            // Do becomes the bounds this run propagated *from*, which is what
            // the pass computed and emphatically not what the state ends up
            // holding. gcs domains have holes, so an inferred bound can snap
            // above the value computed here; recording the snapped value would
            // leave the mandatory self-re-wake with `Vl` empty, and the
            // consequences of the snap would be lost with nothing to show for
            // it. Recording the computed value instead is what puts the snapped
            // node back into `Vl` next time. (`run_hole_snap_test` pins it.)
            for (auto v : memory.bounds_work.settle_order)
                if (memory.bounds_work.settled_bound[v] > memory.do_lb[v]) {
                    memory.trail.push_back(DifferenceTrailEntry{DifferenceTrailKind::LowerGate, v, memory.do_lb[v]});
                    memory.do_lb[v] = memory.bounds_work.settled_bound[v];
                }

            if (incremental.audit) {
                memory.claim = memory.lb_start;
                for (auto v : memory.bounds_work.settle_order)
                    if (memory.bounds_work.settled_bound[v] > memory.claim[v])
                        memory.claim[v] = memory.bounds_work.settled_bound[v];

                memory.pass_bound = memory.lb_start;
                memory.pass_pred.assign(n, nullopt);
                if (relax_lower_bounds(memory.pass_bound, memory.pass_pred, false))
                    throw UnexpectedException{"difference logic incremental propagation missed a negative cycle that the from-scratch pass found"};
                for (size_t v = 0; v < n; ++v)
                    if (memory.claim[v] != memory.pass_bound[v])
                        throw UnexpectedException{"difference logic incremental propagation reached a different lower bound fixpoint from the "
                                                  "from-scratch pass at node " +
                            std::to_string(v) + ": " + memory.claim[v].to_string() + " against " + memory.pass_bound[v].to_string() +
                            ". The incremental pass has lost propagation, which no proof can see."};
            }

            // IncUB is IncLB on the reverse graph with the potential, the bounds
            // and the gate all negated: `ub(x) <= ub(y) + d` is
            // `-ub(x) >= -ub(y) - d`, which is the lower bound relation along
            // the arc read backwards, and `-pi` is a valid potential for it.
            // One implementation, two instantiations, and no second chance to
            // mistranscribe Algorithm 3. All three negated arrays are stored
            // that way rather than rebuilt per call.
            difference_incremental_bounds(n, arcs, memory.by_head, false, memory.active_flags, memory.neg_potential, memory.ub_start_neg,
                memory.do_ub_neg, memory.forced_ub, memory.bounds_work);

            for (auto v : memory.bounds_work.settle_order)
                if (memory.bounds_work.has_predecessor[v] && memory.bounds_work.settled_bound[v] > memory.ub_start_neg[v]) {
                    auto e = memory.bounds_work.predecessor[v];
                    infer_upper_bound(v, -memory.bounds_work.settled_bound[v], e, -memory.bounds_work.settled_bound[arcs[e].to]);
                }

            for (auto v : memory.bounds_work.settle_order)
                if (memory.bounds_work.settled_bound[v] > memory.do_ub_neg[v]) {
                    memory.trail.push_back(DifferenceTrailEntry{DifferenceTrailKind::UpperGate, v, memory.do_ub_neg[v]});
                    memory.do_ub_neg[v] = memory.bounds_work.settled_bound[v];
                }

            if (incremental.audit) {
                memory.claim = memory.ub_start_neg;
                for (auto v : memory.bounds_work.settle_order)
                    if (memory.bounds_work.settled_bound[v] > memory.claim[v])
                        memory.claim[v] = memory.bounds_work.settled_bound[v];
                for (size_t v = 0; v < n; ++v)
                    memory.claim[v] = -memory.claim[v];

                memory.pass_bound.assign(n, 0_i);
                for (size_t v = 0; v < n; ++v)
                    memory.pass_bound[v] = -memory.ub_start_neg[v];
                memory.pass_pred.assign(n, nullopt);
                if (relax_upper_bounds(memory.pass_bound, memory.pass_pred, false))
                    throw UnexpectedException{"difference logic incremental propagation missed a negative cycle that the from-scratch pass found"};
                for (size_t v = 0; v < n; ++v)
                    if (memory.claim[v] != memory.pass_bound[v])
                        throw UnexpectedException{"difference logic incremental propagation reached a different upper bound fixpoint from the "
                                                  "from-scratch pass at node " +
                            std::to_string(v) + ": " + memory.claim[v].to_string() + " against " + memory.pass_bound[v].to_string() +
                            ". The incremental pass has lost propagation, which no proof can see."};
            }

            // Publish the trail: everything pushed above belongs to this epoch,
            // and a backtrack past it will restore this number and undo exactly
            // those entries. Done last, so that a contradiction raised part way
            // through leaves the entries to be undone rather than committed.
            any_cast<size_t &>(state.get_constraint_state(trail_mark_handle)) = memory.trail.size();
        }
    };

    // GCS_DIFFERENCE_AUDIT turns the differential fixpoint audit on for every
    // difference propagator in the process, so a whole corpus can be run under
    // it without touching a single model. Read once.
    auto difference_audit_from_environment() -> bool
    {
        static const bool result = [] {
            const char * e = std::getenv("GCS_DIFFERENCE_AUDIT");
            return e && *e && string{e} != "0";
        }();
        return result;
    }
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

auto gcs::innards::install_difference_propagator(Propagators & propagators, State & initial_state, const ConstraintID & constraint_id,
    DifferenceGraph graph, DifferenceSimplificationOptions simplify, DifferenceIncrementalOptions incremental) -> void
{
    if (graph.edges.empty() && graph.static_bounds.empty() && graph.disallowed_conditions.empty())
        return;

    incremental.audit = incremental.audit || difference_audit_from_environment();

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

    // The only trailed state: how much of the undo trail belongs to the current
    // epoch. State::on_backtrack is not reachable from a propagator's
    // `const State &`, and copying the whole of Do into every epoch would make
    // entering an epoch O(n + m); a single number in the trailed constraint
    // state gives exact restoration at O(1) per epoch instead, unwound lazily at
    // the next call. Lazily is safe precisely because the restored values are
    // exact and do not depend on the current domains --- nothing reads Do
    // between the backtrack and that call.
    auto trail_mark_handle = initial_state.add_constraint_state(size_t{0});

    // The root simplification stage mutates `arcs`, `arc_conditions` and
    // `round_bound` in place, once, on the first call --- hence the `mutable`
    // below. It is safe without trailing for the same reason the paper's section
    // 5.3 boundary is where it is: the stage runs only at the root, before any
    // decision, and every conclusion it draws (this edge is implied by a path of
    // unconditional or root-fixed edges; this node has no edges left) is a
    // statement about the *graph*, which no amount of backtracking changes.
    // Nothing there reads a domain. The incremental machinery below is `mutable`
    // for a different reason, and one the paper is explicit about: the potential
    // function survives backtracking by design.
    propagators.install(
        constraint_id,
        [nodes = move(graph.nodes), arcs = move(arcs), arc_conditions = move(arc_conditions), static_bounds = move(graph.static_bounds),
            disallowed_conditions = move(graph.disallowed_conditions), edge_lines = move(graph.edge_lines), simplify = move(simplify),
            incremental = move(incremental), memory = DifferencePropagatorMemory{}, trail_mark_handle, simplification_pending = true,
            round_bound = number_of_nodes](const State & state, auto & inference, ProofLogger * const logger) mutable -> PropagatorState {
            auto n = nodes.size();
            auto m = arcs.size();

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
            // the state that the passes below seed from. An unconditional one
            // never changes, so after the first call it is a no-op; a
            // conditional one applies from the moment its condition holds, and
            // cites it. Nothing about it needs trailing or gating: a bound it
            // applies moves the state, and moving the state is exactly what puts
            // the node into Vl on this very call.
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

            auto first_call = simplification_pending;
            bool at_root = true;

            if (first_call) {
                simplification_pending = false;

                for ([[maybe_unused]] const auto & guess : state.guesses()) {
                    at_root = false;
                    break;
                }

                run_difference_root_simplification(state, inference, logger, n, arcs, arc_conditions, edge_lines, simplify, round_bound, at_root);
                m = arcs.size();
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

            // The undo trail is popped down to the mark *before* the snapshot,
            // so that the snapshot loop can compare each arc's current activity
            // against the restored record in the same pass. This restores exact
            // values, which is what makes doing it here rather than at the
            // moment of the backtrack sound *and* complete: nothing reads `Do`
            // in between, and what is restored does not depend on the current
            // domains. On the first call the trail is empty and the mark is
            // zero, so this does nothing and the arrays below need not exist
            // yet.
            if (incremental.enabled) {
                auto & mark = any_cast<size_t &>(state.get_constraint_state(trail_mark_handle));
                while (memory.trail.size() > mark) {
                    const auto & entry = memory.trail.back();
                    switch (entry.kind) {
                        using enum DifferenceTrailKind;
                    case LowerGate: memory.do_lb[entry.index] = entry.value; break;
                    case UpperGate: memory.do_ub_neg[entry.index] = entry.value; break;
                    case Activation: memory.arc_was_active[entry.index] = (0_i == entry.value ? 0 : 1); break;
                    }
                    memory.trail.pop_back();
                }
            }

            auto all_active = arc_conditions.empty();
            memory.active_edges.clear();
            memory.changed_arcs.clear();
            if (! all_active) {
                // One pass over the arcs, doing everything a conditional system
                // needs: the flags the adjacency traversals filter on, the index
                // list the from-scratch relaxation walks, and the list of arcs
                // whose activity differs from what the incremental machinery has
                // established its invariants for. Three separate passes here was
                // 10-15% on the half-reified RCPSP/max instances, where the
                // conditional edges make `m` an order of magnitude larger than
                // `n` and these passes are the whole cost of a wake.
                auto detect_changes = incremental.enabled && ! first_call;
                memory.active_edges.reserve(m);
                memory.active_flags.resize(m);
                for (size_t e = 0; e < m; ++e) {
                    char active = (! arc_conditions[e] || LiteralIs::DefinitelyTrue == state.test_literal(*arc_conditions[e])) ? 1 : 0;
                    memory.active_flags[e] = active;
                    if (active)
                        memory.active_edges.push_back(e);
                    if (detect_changes && active != memory.arc_was_active[e])
                        memory.changed_arcs.push_back(e);
                }
            }
            else
                memory.active_flags.clear();

            DifferenceCall<std::remove_reference_t<decltype(inference)>> call{state, inference, logger, nodes, arcs, arc_conditions, edge_lines,
                incremental, memory, trail_mark_handle, n, m, round_bound, all_active};

            if (incremental.enabled)
                call.run_incremental(first_call, at_root);
            else
                call.run_from_scratch();

            // Deliberately not EnableButIdempotent, and not merely because the
            // scope aliases whenever one variable appears in several edges
            // (which is the normal case here, and which Propagators::install
            // detects and ignores the claim for anyway). The claim would be
            // wrong on its own terms: the passes above reach the fixpoint of the
            // bounds abstraction, but an inferred bound can snap past a hole in
            // the domain and land strictly above the value computed there, which
            // seeds the next call higher and lets it push further. So a second
            // call genuinely can infer more, and the propagator has to be
            // re-woken by its own inferences until the state settles.
            // (run_hole_snap_test in difference_constraints_test.cc pins this,
            // for both routes.)
            return PropagatorState::Enable;
        },
        triggers);
}
