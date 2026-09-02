#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/all_different/encoding.hh>
#include <gcs/constraints/all_different/vc_all_different.hh>
#include <gcs/constraints/circuit/hints.hh>
#include <gcs/constraints/circuit/subcircuit.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/am1_from_pairs.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>

#include <util/enumerate.hh>
#include <util/overloaded.hh>

#include <algorithm>
#include <any>
#include <map>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#else
#include <fmt/core.h>
#endif

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::innards::subcircuit;

using gcs::subcircuit::Check;
using gcs::subcircuit::Prevent;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
#else
using fmt::format;
#endif

using std::cmp_equal;
using std::cmp_greater_equal;
using std::cmp_not_equal;
using std::make_optional;
using std::make_unique;
using std::map;
using std::nullopt;
using std::optional;
using std::size_t;
using std::string;
using std::to_string;
using std::unique_ptr;
using std::vector;

namespace
{
    // The membership sum: how many nodes are on the tour. A node off the tour points at
    // itself, so this is just a count of the "not a self loop" literals, which means the
    // tour's length is a linear expression over literals the solver already has and needs
    // no auxiliary variable of its own. That is what keeps the wrap-around row linear.
    auto tour_size_sum(const vector<IntegerVariableID> & succ) -> WPBSum
    {
        WPBSum sum;
        for (const auto & [idx, s] : enumerate(succ))
            sum += 1_i * (s != Integer(static_cast<long long>(idx)));
        return sum;
    }

    // One walk of the graph of fixed successor edges, splitting it into the closed cycles
    // and the open chains. Self loops are their own one-node cycles: a node pointing at
    // itself is off the tour, so it neither closes anything nor blocks anything.
    struct FixedEdges
    {
        // Each cycle, in order, as visited. Length one means a self loop.
        vector<vector<long>> cycles;
        // Each maximal open chain, in order: chain.front() has no fixed predecessor and
        // chain.back()'s successor is not yet fixed.
        vector<vector<long>> chains;
    };

    auto walk_fixed_edges(const vector<IntegerVariableID> & succ, const State & state) -> FixedEdges
    {
        auto n = static_cast<long>(succ.size());
        auto fixed = vector<optional<long>>(n, nullopt);
        auto has_fixed_pred = vector<bool>(n, false);
        for (long i = 0; i < n; ++i)
            if (auto v = state.optional_single_value(succ[i])) {
                fixed[i] = v->raw_value;
                has_fixed_pred[v->raw_value] = true;
            }

        FixedEdges result;
        auto seen = vector<bool>(n, false);

        // Open chains first: they start at a fixed edge whose tail nothing points at.
        for (long i = 0; i < n; ++i) {
            if (! fixed[i] || has_fixed_pred[i] || seen[i])
                continue;
            vector<long> chain{i};
            seen[i] = true;
            auto j = *fixed[i];
            while (true) {
                // A node is only ever reached once from a chain start, because a node with
                // a fixed predecessor is not a chain start -- unless two successors are
                // fixed to the same value, which the all-different pass above rejects. If
                // it somehow happens anyway, stop rather than following the loop forever:
                // circuit_base.cc guards the same spot for the same reason.
                if (seen[j])
                    break;
                chain.emplace_back(j);
                seen[j] = true;
                if (! fixed[j])
                    break;
                j = *fixed[j];
            }
            result.chains.emplace_back(std::move(chain));
        }

        // Whatever still has a fixed successor and has not been seen is on a cycle.
        for (long i = 0; i < n; ++i) {
            if (! fixed[i] || seen[i])
                continue;
            vector<long> cycle;
            auto j = i;
            auto closed = false;
            do {
                cycle.emplace_back(j);
                seen[j] = true;
                j = *fixed[j];
                if (j == i) {
                    closed = true;
                    break;
                }
            } while (! seen[j]);

            // The walk can only fail to come back to where it started if two successors
            // are fixed to the same value, which the all-different pass above rejects. Drop
            // the walk rather than hand a certificate a list of edges that are not all
            // really there.
            if (closed)
                result.cycles.emplace_back(std::move(cycle));
        }

        return result;
    }

    // Francis and Stuckey's evidence node: one that cannot be a self loop, and so must be
    // on the tour. Without one, a closed cycle is not yet wrong -- every other node might
    // still opt out -- so nothing at all can be inferred. Returns the lowest-numbered such
    // node outside `exclude`, which is their default choice.
    auto find_evidence_node(const vector<IntegerVariableID> & succ, const State & state, const vector<bool> & exclude) -> optional<long>
    {
        for (const auto & [idx, s] : enumerate(succ)) {
            auto i = static_cast<long>(idx);
            if (exclude[i])
                continue;
            if (! state.in_domain(s, Integer{i}))
                return i;
        }
        return nullopt;
    }
}

namespace
{
    // Derive, at the current proof level, that the tour holds at most `cycle.size()` nodes
    // given the assignments round `cycle`.
    //
    // Two cases have to be covered, and they pull in opposite directions:
    //
    //  * no node of the cycle is `first`, so every edge takes its step row, and chaining
    //    those round the cycle telescopes to 0 >= |cycle|, which is absurd;
    //  * some node a of the cycle is `first`, so the edge into a takes its wrap row
    //    instead, and chaining telescopes to |tour| <= |cycle|.
    //
    // Adding the first row to each of the others resolves away the `first` flags, leaving
    // the bound with no case still open. Circuit needs none of this: its anchor is node 0,
    // so it always knows statically which edge is the wrap edge.
    auto derive_tour_at_most(ProofLogger & logger, const SubCircuitPosData & pos_data, const vector<long> & cycle) -> void
    {
        auto k = cycle.size();
        auto next = [&](size_t t) { return cycle[(t + 1) % k]; };

        // Running-saturate, as circuit_scc.cc does: the first push is plain, every
        // subsequent one is followed by `s`, because these sums are not clause-shaped and
        // an intermediate saturation can shrink coefficients usefully.
        auto add_sat = [](PolBuilder & p, ProofLine line) -> PolBuilder & { return p.empty() ? p.add(line) : p.add(line).saturate(); };

        if (! pos_data.defined)
            throw UnexpectedException{"SubCircuit tried to justify an inference with no position encoding"};

        // One comment for the whole derivation rather than one per case: there are
        // |cycle| + 1 cases and a proof comment costs bytes at every firing.
        if (pos_data.anchor) {
            // With the tour anchored at a named node, which edge wraps is known, so there
            // is nothing to split over: one polish-notation step either way.
            if (std::find(cycle.begin(), cycle.end(), *pos_data.anchor) == cycle.end()) {
                // Every edge of the cycle steps, and chaining them telescopes to 0 >= k.
                // The cycle cannot exist at all -- no evidence node needed, because the
                // anchor is itself a node outside it that has to be on the tour.
                logger.emit_proof_comment(format("this cycle of {} misses the anchor entirely", k));
                PolBuilder avoids_anchor;
                for (size_t t = 0; t < k; ++t)
                    add_sat(avoids_anchor, *pos_data.edges.at(cycle[t]).at(next(t)).step_ge);
                avoids_anchor.emit(logger, ProofLevel::Current);
            }
            else {
                // The edge into the anchor is the wrap; chaining the rest bounds the tour.
                logger.emit_proof_comment(format("this cycle of {} contains the anchor, so it is the whole tour", k));
                PolBuilder is_whole_tour;
                for (size_t t = 0; t < k; ++t) {
                    const auto & lines = pos_data.edges.at(cycle[t]).at(next(t));
                    add_sat(is_whole_tour, next(t) == *pos_data.anchor ? *lines.wrap_le : *lines.step_le);
                }
                is_whole_tour.emit(logger, ProofLevel::Current);
            }
            return;
        }

        // Unanchored, so every node of the cycle is a candidate for being first.
        logger.emit_proof_comment(format("this cycle of {} bounds the whole tour, whichever of its nodes is first", k));

        PolBuilder no_first;
        for (size_t t = 0; t < k; ++t)
            add_sat(no_first, *pos_data.edges.at(cycle[t]).at(next(t)).step_ge);

        PolBuilder combine;
        combine.add(no_first.emit(logger, ProofLevel::Current));
        for (size_t s = 0; s < k; ++s) {
            PolBuilder this_first;
            for (size_t t = 0; t < k; ++t) {
                const auto & lines = pos_data.edges.at(cycle[t]).at(next(t));
                add_sat(this_first, next(t) == cycle[s] ? *lines.wrap_le : *lines.step_le);
            }
            add_sat(combine, this_first.emit(logger, ProofLevel::Current));
        }

        combine.emit(logger, ProofLevel::Current);
    }

    // The tour size: how many nodes do not point at themselves. All of this follows from
    // the one cardinality row define_proof_model() writes, so every inference here is a
    // plain RUP against it.
    //
    // Not inferred, deliberately: the count can never be 1, because a lone node on the
    // tour has nowhere to point but itself. That is a consequence of the rest of the model
    // rather than something the encoding says, so it would have to be derived in the proof
    // rather than read off a row, and nothing needs it yet.
    auto propagate_tour_size(const vector<IntegerVariableID> & succ, const ConstraintID & owner, const IntegerVariableID & size,
        const vector<IntegerVariableID> & reason_vars, const State & state, auto & inference, ProofLogger * const logger) -> void
    {
        auto n = static_cast<long long>(succ.size());
        long long on = 0, off = 0;
        for (const auto & [idx, s] : enumerate(succ)) {
            auto here = Integer(static_cast<long long>(idx));
            if (! state.in_domain(s, here))
                ++on; // cannot be a self loop, so it is on the tour whatever else happens
            else if (state.optional_single_value(s) == here)
                ++off; // fixed as a self loop, so it is off the tour
        }

        auto reason = generic_reason(reason_vars);
        inference.infer(logger, size >= Integer{on}, JustifyUsingRUP{hints::SubCircuit{owner}}, reason);
        inference.infer(logger, size <= Integer{n - off}, JustifyUsingRUP{hints::SubCircuit{owner}}, reason);

        // With a bound tight against what is already decided, every undecided node goes
        // the same way: no room left for another node on the tour, or none left off it.
        auto force_undecided = [&](bool onto_tour) {
            vector<Literal> forced;
            for (const auto & [idx, s] : enumerate(succ)) {
                auto here = Integer(static_cast<long long>(idx));
                if (! state.in_domain(s, here) || state.optional_single_value(s) == here)
                    continue;
                forced.emplace_back(onto_tour ? Literal{s != here} : Literal{s == here});
            }
            if (! forced.empty())
                inference.infer_all(logger, forced, JustifyUsingRUP{hints::SubCircuit{owner}}, reason);
        };

        if (state.upper_bound(size) == Integer{on})
            force_undecided(false);
        else if (state.lower_bound(size) == Integer{n - off})
            force_undecided(true);
    }

    // Everything on the tour is reachable from the anchor, because the tour is one cycle
    // through it. So anything the anchor cannot reach has to opt out. This is the
    // connectivity core of Francis and Stuckey's `scc`, and their observation that this
    // family cannot say anything until some node is mandatory is why it is guarded on the
    // anchor: without one there is nothing to be reachable from.
    //
    // Self loops are not tour edges -- a node pointing at itself is off the tour -- so they
    // are not followed, which is the same care F&S call for: "self-cycle edges must be
    // handled carefully... ignored when finding the children of a node".
    auto reachable_layers(const vector<IntegerVariableID> & succ, const long anchor, const State & state) -> vector<vector<bool>>
    {
        auto n = succ.size();
        // layers[t][x]: x is reachable from the anchor in at most t steps. The certificate
        // walks these out one at a time, so it needs each layer and not just the union.
        auto layers = vector<vector<bool>>(n, vector<bool>(n, false));
        layers[0][static_cast<size_t>(anchor)] = true;
        for (size_t t = 1; t < n; ++t) {
            layers[t] = layers[t - 1];
            for (size_t i = 0; i < n; ++i) {
                if (! layers[t - 1][i])
                    continue;
                for (const auto & v : state.each_value_immutable(succ[i])) {
                    auto j = static_cast<size_t>(v.raw_value);
                    if (cmp_not_equal(j, i))
                        layers[t][j] = true;
                }
            }
        }
        return layers;
    }

    // The other half of the same fact. The tour is a cycle *through* the anchor, so a node
    // on it does not merely have to be reachable from the anchor, it has to reach the anchor
    // back; anything that cannot has to opt out. Between them the two directions say the
    // tour lies inside the anchor's strongly connected component, which is Francis and
    // Stuckey's rule for a strongly connected sub-component containing a required node,
    // specialised to the one component that always has such a node in it.
    //
    // Self loops are not followed here either, and for the same reason: a node pointing at
    // itself is off the tour, so that is not a tour edge to travel along.
    auto reaches_anchor(const vector<IntegerVariableID> & succ, const long anchor, const State & state) -> vector<bool>
    {
        auto n = succ.size();

        // The reverse graph, built once. A breadth-first walk backwards from the anchor is
        // then one pass over it, where iterating the forward domains to a fixpoint would
        // walk them once per layer.
        auto backwards = vector<vector<size_t>>(n);
        for (size_t i = 0; i < n; ++i)
            for (const auto & v : state.each_value_immutable(succ[i])) {
                auto j = static_cast<size_t>(v.raw_value);
                if (cmp_not_equal(j, i))
                    backwards[j].emplace_back(i);
            }

        auto reaches = vector<bool>(n, false);
        reaches[static_cast<size_t>(anchor)] = true;
        auto pending = vector<size_t>{static_cast<size_t>(anchor)};
        while (! pending.empty()) {
            auto here = pending.back();
            pending.pop_back();
            for (const auto & before : backwards[here])
                if (! reaches[before]) {
                    reaches[before] = true;
                    pending.emplace_back(before);
                }
        }

        return reaches;
    }

    // At most one of the successors takes value v. The all-different encoding only has the
    // pairwise rows, so the clique inequality over them has to be derived -- which is
    // recover_am1_from_pairs's job, so all there is to do here is emit the pairs it merges
    // and remember the answer.
    //
    // This was a hand-rolled staircase until it turned out to be the fifth copy of one
    // derivation, four of which predate the shared version. Not for the reason the shared
    // version's own documentation gives, though, which is worth recording because the next
    // caller to switch over will read it: recover_am1_from_pairs pins its result with an
    // `ia` step, on the grounds that every intermediate is sound whatever it is fed, so a
    // corrupted merge lands on a weaker line VeriPB is right to accept. *At this call site
    // that pin buys nothing*, measured rather than assumed -- the pigeonhole below consumes
    // this line coefficient by coefficient, so a merge that lost an input, summed
    // everything at once, or skipped the final division is already rejected downstream,
    // hand-rolled and unpinned, in all four cases tried. What the switch does buy is one
    // derivation instead of five, a refusal rather than an operandless `pol` below two
    // members, and the induction's scaffolding deleted rather than left live. It costs 0.7%
    // more `.pbp`.
    auto need_value_at_most_one(ProofLogger & logger, const vector<IntegerVariableID> & succ, SCCProofCache & cache, const long v) -> ProofLine
    {
        if (auto found = cache.value_at_most_one.find(v); found != cache.value_at_most_one.end())
            return found->second;

        // The lower triangle, in the order the induction consumes it.
        vector<ProofLiteralOrFlag> members;
        auto at_most_ones = vector<vector<ProofLine>>(succ.size());
        for (size_t j = 0; j < succ.size(); ++j) {
            members.emplace_back(succ[j] == Integer{v});
            for (size_t i = 0; i < j; ++i)
                at_most_ones[j].emplace_back(logger.emit_rup_proof_line(
                    WPBSum{} + 1_i * ! (succ[i] == Integer{v}) + 1_i * ! (succ[j] == Integer{v}) >= 1_i, ProofLevel::Temporary));
        }

        auto line = recover_am1_from_pairs(logger, members, at_most_ones, ProofLevel::Top);
        cache.value_at_most_one.emplace(v, line);
        return line;
    }

    // At least one of the successors takes value v: pigeonhole. Every successor takes some
    // value, and every value other than v can be taken by at most one of them, so with as
    // many successors as values somebody has to take v. This is what makes the reachability
    // induction below possible at all -- it is how "the node at position t has a
    // predecessor" gets said.
    auto need_value_at_least_one(ProofLogger & logger, const vector<IntegerVariableID> & succ, SCCProofCache & cache, const long v) -> ProofLine
    {
        if (auto found = cache.value_at_least_one.find(v); found != cache.value_at_least_one.end())
            return found->second;

        PolBuilder pigeonhole;
        for (const auto & s : succ)
            pigeonhole.add(logger.names_and_ids_tracker().need_constraint_saying_variable_takes_at_least_one_value(s));
        for (size_t w = 0; w < succ.size(); ++w)
            if (cmp_not_equal(w, v))
                pigeonhole.add(need_value_at_most_one(logger, succ, cache, static_cast<long>(w)));

        auto line = pigeonhole.emit(logger, ProofLevel::Top);
        cache.value_at_least_one.emplace(v, line);
        return line;
    }

    // Justify "node m cannot be on the tour" for every m the anchor cannot reach, by walking
    // out from the anchor one layer at a time.
    //
    // The fact derived at each layer t, for each node x the anchor has not reached within t
    // steps, is
    //
    //     E(t, x):  pos[x] = t  ->  succ[x] = x
    //
    // "x sitting at position t has to be off the tour". Its proof is the same at every
    // layer. Somebody is x's predecessor, and for each candidate q either q = x, which is
    // the conclusion, or the step row puts q at position t-1. A q the anchor *had* reached
    // within t-1 steps cannot point at x, or x would have been reached within t; that is in
    // the reason. A q it had not reached carries E(t-1, q), so q at t-1 is off the tour and
    // cannot point at x either. At t = 0 the step row puts q at position -1, which the
    // position variable's own lower bound refuses, so the layer needs nothing before it.
    //
    // Two things make this work here where circuit_scc.cc's argument would not. Positions
    // are anchored on the very node the walk starts from, so no shifting to an arbitrary
    // root is needed -- and that shift would be modulo the tour's length, which is a
    // variable. And a node off the tour sits at position zero, so position t >= 1 already
    // means on the tour and nothing has to count how long the tour is.
    //
    // The whole thing is a chain of RUP lemmas with exactly one cutting-planes step in it,
    // the pigeonhole for "somebody is x's predecessor". Nothing else needs a `pol`, and
    // nothing has to cite a step row either, which is worth stating because the arithmetic
    // looks as though it should need both: taking "x is at t" through the step row to "q is
    // at t-1" is unit propagation on the two halves of that row. The row is written over
    // `pos[x] - pos[q]`, so with `pos[x]` fixed at t the `>=` half gives `pos[q] <= t-1` and
    // the `<=` half gives `pos[q] >= t-1` -- the `>=` half is the one bounding q from above,
    // which is the opposite way round from how it reads -- and between them they pin every
    // bit. Those halves are model rows, so unit propagation reaches them unaided -- and
    // only because the encoding is anchored, since without an anchor each is guarded on a
    // `first` flag as well, which nothing here would have fixed. Adding pols to help was
    // measured and they were dead weight: each one removed leaves every test verifying,
    // while a plain JustifyUsingRUP in place of this function still gets rejected, so it is
    // these lemmas and not the arithmetic that is load-bearing. Dropping the pigeonhole
    // does make VeriPB reject.
    auto derive_unreachable(ProofLogger & logger, const vector<IntegerVariableID> & succ, const SubCircuitPosData & pos_data, SCCProofCache & cache,
        const vector<vector<bool>> & reached_within, const ReasonLiterals & reason) -> void
    {
        auto n = succ.size();
        logger.emit_proof_comment("everything on the tour is reachable from the anchor, one layer at a time");

        for (size_t t = 0; t < n; ++t)
            for (size_t x = 0; x < n; ++x) {
                if (reached_within[t][x] || cmp_equal(x, *pos_data.anchor))
                    continue;

                auto at_t = pos_data.pos.at(static_cast<long>(x)) == Integer(static_cast<long long>(t));

                // "Somebody is x's predecessor" is not in the encoding -- the all-different
                // rows are a pairwise clique, which is at-most-one only -- so it has to be
                // derived, and it is what the layer's conclusion resolves the candidates
                // against. Emitted for its place in the database rather than for its line
                // number, at ProofLevel::Top and cached, so a later layer and a later search
                // node both reuse it.
                need_value_at_least_one(logger, succ, cache, static_cast<long>(x));

                for (size_t q = 0; q < n; ++q) {
                    if (q == x)
                        continue;

                    // A predecessor the anchor had already reached cannot point at x -- x
                    // would have been reached too -- and that is in the reason, so unit
                    // propagation has it without any help.
                    if (t > 0 && reached_within[t - 1][q])
                        continue;
                    // Nor can the anchor itself, for the same reason, and it carries no
                    // E(t-1, .) of its own.
                    if (cmp_equal(q, *pos_data.anchor))
                        continue;

                    logger.emit_rup_proof_line_under_reason(
                        reason, WPBSum{} + 1_i * ! at_t + 1_i * ! (succ[q] == Integer(static_cast<long long>(x))) >= 1_i, ProofLevel::Temporary);
                }

                // E(t, x) itself, at ProofLevel::Current so that the next layer still has it:
                // that is how the layers chain, and why nothing has to restate a layer.
                logger.emit_rup_proof_line_under_reason(
                    reason, WPBSum{} + 1_i * ! at_t + 1_i * (succ[x] == Integer(static_cast<long long>(x))) >= 1_i, ProofLevel::Current);
            }
    }

    // Justify "node m cannot be on the tour" for every m that cannot reach the anchor. The
    // fact derived for each such node x, at each position t, is
    //
    //     G(t, x):  pos[x] = t  ->  succ[x] = x
    //
    // the same shape as the forward walk's E(t, x) and the same length of induction, but it
    // runs the other way: t from n-1 down to 0, because here it is what x's successor does
    // that settles x, not what its predecessor does.
    //
    // Its proof. succ[x] takes some value, and every candidate y other than x cannot reach
    // the anchor either -- if y could then x could, through y -- so a candidate that can is
    // excluded by the reason. For one that cannot, the step row puts y at position t+1, and
    // G(t+1, y) then makes y a self loop; value y would be taken twice, by succ[x] and by
    // succ[y], which the all-different rows forbid. At t = n-1 the step row asks for
    // position n, which the position variable's own upper bound refuses, so the top layer
    // needs nothing above it.
    //
    // This direction needs no derivation of its own at all -- no pigeonhole and no cutting
    // planes anywhere -- because every fact it leans on is a row of the model: the two
    // halves of the step row, one all-different pair, and the at-least-one-value row for
    // succ[x]. Following x's own successor is what buys that. The forward walk cannot,
    // because hunting for x's *predecessor* asks that somebody take the value x, and only
    // at-most-one of those is written down. So on an instance where both fire, this half is
    // very nearly free.
    auto derive_cannot_reach_anchor(ProofLogger & logger, const vector<IntegerVariableID> & succ, const SubCircuitPosData & pos_data,
        const vector<bool> & reaches, const ReasonLiterals & reason) -> void
    {
        auto n = static_cast<long long>(succ.size());
        logger.emit_proof_comment("everything on the tour reaches the anchor, working down from the last position");

        for (auto t = n - 1; t >= 0; --t)
            for (long long x = 0; x < n; ++x) {
                if (reaches[static_cast<size_t>(x)])
                    continue;

                auto at_t = pos_data.pos.at(static_cast<long>(x)) == Integer{t};

                for (long long y = 0; y < n; ++y) {
                    // A candidate that reaches the anchor is excluded by the reason, and so
                    // is anything outside the domain; the anchor itself reaches itself, so it
                    // is never a candidate here, which is why the step row this leans on is
                    // always the step row and never the wrap one.
                    if (y == x || reaches[static_cast<size_t>(y)])
                        continue;

                    logger.emit_rup_proof_line_under_reason(
                        reason, WPBSum{} + 1_i * ! at_t + 1_i * ! (succ[static_cast<size_t>(x)] == Integer{y}) >= 1_i, ProofLevel::Temporary);
                }

                // G(t, x) itself, at ProofLevel::Current so the layer below still has it.
                logger.emit_rup_proof_line_under_reason(
                    reason, WPBSum{} + 1_i * ! at_t + 1_i * (succ[static_cast<size_t>(x)] == Integer{x}) >= 1_i, ProofLevel::Current);
            }
    }

    auto propagate_subcircuit(const vector<IntegerVariableID> & succ, const ConstraintID & owner, const SubCircuitPosData & pos_data,
        const ConstraintStateHandle & unassigned_handle, const bool prevent, const optional<long> & scc_anchor,
        const std::shared_ptr<SCCProofCache> & cache, const State & state, auto & inference, ProofLogger * const logger) -> void
    {
        if (! propagate_non_gac_alldifferent(unassigned_handle, state, inference, logger, owner))
            return;

        auto n = succ.size();
        // One walk per call, from scratch. circuit::Prevent keeps its chain endpoints in
        // backtrackable state and folds each newly fixed edge in in O(1); nothing here
        // needs that yet, and a from-scratch walk is much easier to read, but it is the
        // obvious thing to do if this ever shows up in a profile.
        auto edges = walk_fixed_edges(succ, state);

        // Given the nodes that may still be on the tour, the literals saying everything else
        // is off it. All three rules below end this way, differing only in how they work out
        // that first set.
        //
        // A node already sitting on its own index is the only one skipped: one fixed to
        // anything else has to go through infer() so that the contradiction is raised and
        // justified. That is the whole of what makes `check` complete -- Francis and Stuckey
        // report failure exactly when a node outside the cycle cannot be a self cycle, and a
        // node fixed elsewhere cannot.
        auto off_tour = [&](const vector<bool> & maybe_on_tour) {
            vector<Literal> off;
            for (size_t m = 0; m < n; ++m) {
                if (maybe_on_tour[m])
                    continue;
                auto here = Integer(static_cast<long long>(m));
                if (state.optional_single_value(succ[m]) == here)
                    continue;
                off.emplace_back(succ[m] == here);
            }
            return off;
        };

        // A closed cycle of two or more nodes is the whole tour, so every other node has
        // to be a self loop. This is Francis and Stuckey's `check`: for Circuit a short
        // cycle is a flat contradiction, but here it only pins down everyone else.
        for (const auto & cycle : edges.cycles) {
            if (cycle.size() < 2)
                continue; // a self loop says only that its own node is off the tour

            auto on_cycle = vector<bool>(n, false);
            for (auto v : cycle)
                on_cycle[v] = true;

            // Nothing left to say if the cycle is the whole graph, or everyone else is
            // already a self loop.
            auto off = off_tour(on_cycle);
            if (off.empty())
                continue;

            auto justf = [&, cycle](const ReasonLiterals &) { derive_tour_at_most(*logger, pos_data, cycle); };
            inference.infer_all(logger, off, JustifyExplicitly{justf, ThenRUP::Yes, hints::SubCircuit{owner}}, generic_reason(succ));
        }

        // Anything the anchor cannot reach has to opt out, and so does anything that cannot
        // reach the anchor back. The two are separate arguments over separate walks, so they
        // are two inferences; the second is taken over the state the first leaves behind,
        // which is the stronger place to take it from and costs nothing, since a node the
        // first has just made a self loop cannot reach anything at all.
        if (scc_anchor) {
            auto layers = reachable_layers(succ, *scc_anchor, state);
            if (auto unreachable = off_tour(layers.back()); ! unreachable.empty()) {
                auto justf = [&](const ReasonLiterals & reason) { derive_unreachable(*logger, succ, pos_data, *cache, layers, reason); };
                inference.infer_all(logger, unreachable, JustifyExplicitly{justf, ThenRUP::Yes, hints::SubCircuit{owner}}, generic_reason(succ));
            }

            auto reaches = reaches_anchor(succ, *scc_anchor, state);
            if (auto stranded = off_tour(reaches); ! stranded.empty()) {
                auto justf = [&](const ReasonLiterals & reason) { derive_cannot_reach_anchor(*logger, succ, pos_data, reaches, reason); };
                inference.infer_all(logger, stranded, JustifyExplicitly{justf, ThenRUP::Yes, hints::SubCircuit{owner}}, generic_reason(succ));
            }
        }

        if (! prevent)
            return;

        // Now the lookahead. A chain of fixed edges must not close into a cycle while some
        // node outside it cannot be a self loop -- that node would have nowhere to go. With
        // no such evidence node there is nothing to infer, because the chain closing and
        // everyone else opting out is a perfectly good solution.
        for (const auto & chain : edges.chains) {
            auto on_chain = vector<bool>(n, false);
            for (auto v : chain)
                on_chain[v] = true;

            if (! find_evidence_node(succ, state, on_chain))
                continue;

            auto start = chain.front();
            auto end = chain.back();
            if (! state.in_domain(succ[end], Integer{start}))
                continue;

            auto closed = chain;
            auto justf = [&, closed](const ReasonLiterals &) { derive_tour_at_most(*logger, pos_data, closed); };
            inference.infer(
                logger, succ[end] != Integer{start}, JustifyExplicitly{justf, ThenRUP::Yes, hints::SubCircuit{owner}}, generic_reason(succ));
        }
    }
}

SubCircuit::SubCircuit(vector<IntegerVariableID> succ) : _succ(std::move(succ))
{
    // As Circuit: two slots pinned to the same constant are a valid (if trivially
    // infeasible) model, so only reject true variable aliasing.
    for (size_t i = 0; i < _succ.size(); ++i) {
        if (is_constant_variable(_succ[i]))
            continue;
        for (size_t j = i + 1; j < _succ.size(); ++j)
            if (_succ[i] == _succ[j])
                throw InvalidProblemDefinitionException{"SubCircuit: successor array contains the same variable handle twice"};
    }
}

auto SubCircuit::with_algorithm(SubCircuitAlgorithm algorithm) -> SubCircuit &
{
    _algorithm = algorithm;
    return *this;
}

auto SubCircuit::with_gac_all_different(optional<bool> enable) -> SubCircuit &
{
    _gac_all_different = enable.value_or(true);
    return *this;
}

auto SubCircuit::with_required_node(long node) -> SubCircuit &
{
    // The range is checkable here, so check it here: a caller who has miscounted finds out
    // at the call rather than when search starts. Whether the node is really declared on
    // the tour needs the initial domains, so that one waits for prepare().
    if (node < 0 || cmp_greater_equal(node, _succ.size()))
        throw InvalidProblemDefinitionException{"SubCircuit: with_required_node() names a node outside the successor array"};
    _required_node = node;
    return *this;
}

auto SubCircuit::with_tour_size(IntegerVariableID size) -> SubCircuit &
{
    _tour_size = size;
    return *this;
}

auto SubCircuit::prepare(Propagators & propagators, State & initial_state, ProofModel * const model) -> bool
{
    for (const auto & s : _succ) {
        propagators.define_bound(initial_state, model, s, Bound::Lower, 0_i);
        propagators.define_bound(initial_state, model, s, Bound::Upper, Integer(static_cast<long long>(_succ.size() - 1)));
    }

    // As Circuit: the GAC all-different is a child constraint, so it can only be installed
    // from here, and it must carry this constraint's identity or two SubCircuits in one
    // problem would share its labelled rows and pair selectors (issue #449). The non-GAC
    // alternative is pure encoding and lives in define_proof_model().
    if (_gac_all_different) {
        AllDifferent all_diff{_succ};
        all_diff.set_constraint_id(constraint_id());
        std::move(all_diff).install(propagators, initial_state, model);
    }

    // The named node has to be declared on the tour, not merely constrained onto it by
    // something posted later: the anchored encoding below is only sound if it really is on
    // the tour, and a constraint posted after this one has not narrowed anything yet when
    // define_proof_model() runs. A declared domain has, since domains are set when the
    // variable is created.
    if (_required_node && initial_state.in_domain(_succ[static_cast<size_t>(*_required_node)], Integer{*_required_node}))
        throw InvalidProblemDefinitionException{
            "SubCircuit: with_required_node() names a node whose own index is still in its successor's domain, so it is not declared "
            "to be on the tour"};

    // A node is on the tour exactly when it does not point at itself, so any node whose own
    // index is already out of its successor's domain is one, and that is all an anchor has
    // to be. So look for one rather than waiting to be told: an anchor halves the number of
    // position rows, gives `check` a contradiction where it would otherwise have to hunt for
    // an evidence node, and is what the SCC arm needs to say anything at all.
    //
    // The lowest-numbered one, because something has to be picked and nothing has measured a
    // better rule; F&S §5.3.3 report that for `circuit` a *random* root is best for their
    // `scc`, which is worth revisiting if the pruning rules ever land, but it is a choice
    // about search and this one is also a choice about the encoding.
    //
    // Only the declared domains can be read here, which is why models differ in whether this
    // finds anything. Both challenge families that use subcircuit pin a node, but only one
    // pins it where this can see: mario writes `succ[LuigiHouse] = MarioHouse`, which the
    // flattener folds into the array as a constant, while tpp writes `succ[n] != n`, which
    // survives as an int_ne over a variable whose declared domain is still full by the time
    // the redefinition has shifted it to be zero-based.
    _anchor = _required_node;
    if (! _anchor)
        for (size_t i = 0; i < _succ.size(); ++i)
            if (! initial_state.in_domain(_succ[i], Integer(static_cast<long long>(i)))) {
                _anchor = static_cast<long>(i);
                break;
            }

    NonGacAllDifferentUnassigned unassigned{};
    for (auto v : _succ)
        unassigned.emplace_back(v);
    _state_handles.unassigned = initial_state.add_constraint_state(unassigned);

    return true;
}

auto SubCircuit::define_proof_model(ProofModel & model, const State &) -> void
{
    if (! _gac_all_different)
        define_clique_not_equals_encoding(model, _constraint_id, _succ);

    if (_succ.empty()) {
        // No node, so no node is on the tour. Anything else the caller asked for still has
        // to be said: an empty array with a tour size pins that size to zero.
        if (_tour_size)
            model.add_labelled_constraint(_constraint_id, "tour_size_le", "tour_size_ge", WPBSum{} + 1_i * *_tour_size == 0_i);
        return;
    }

    auto n = static_cast<long>(_succ.size());
    auto tour_size = tour_size_sum(_succ);

    if (_tour_size)
        model.add_labelled_constraint(_constraint_id, "tour_size_le", "tour_size_ge", tour_size + -1_i * *_tour_size == 0_i);
    auto & data = _pos_data;
    data.defined = true;

    for (long i = 0; i < n; ++i)
        data.pos.emplace(i, model.create_proof_only_integer_variable(0_i, Integer{n - 1}, "subpos", IntegerVariableProofRepresentation::Bits));

    data.anchor = _anchor;

    if (data.anchor) {
        // Anchored: the tour starts at the named node, so the only edges that can wrap are
        // the ones into it. No `first` flags are needed at all.
        model.add_labelled_constraint(_constraint_id, "anchor_pos", WPBSum{} + 1_i * data.pos.at(*data.anchor) <= 0_i);
    }
    else {
        // first[i]: node i is on the tour and every lower-numbered node is off it, written
        // as "all i+1 of these literals hold". Fully reified, so unit propagation fixes the
        // flag from the successors -- a half-reified flag would leave it free on a solution
        // and the rows below that need it would not check.
        for (long i = 0; i < n; ++i) {
            auto conjunction = WPBSum{} + 1_i * (_succ[i] != Integer{i});
            for (long j = 0; j < i; ++j)
                conjunction += 1_i * (_succ[j] == Integer{j});
            data.first.emplace(i, model.create_proof_flag_fully_reifying(_constraint_id, {i}, "first", conjunction >= Integer{i + 1}));
        }

        // The tour starts at whichever node is first...
        for (long i = 0; i < n; ++i)
            data.first_is_zero.emplace(i,
                model.add_labelled_constraint(_constraint_id, "first_pos_" + to_string(i), WPBSum{} + 1_i * data.pos.at(i) <= 0_i,
                    HalfReifyOnConjunctionOf{{data.first.at(i)}}));
    }

    // ...and a node off the tour is given position zero. Nothing here needs the positions to
    // be a permutation -- no certificate below relies on them being distinct -- and an
    // off-tour node takes part in no position row at all: it has no successor other than
    // itself, and by all-different nothing else can point at it either. So the only job
    // these rows have is to leave `pos` determined by the successors under unit propagation,
    // which is what solution checking needs, and zero does that as well as anything.
    //
    // The stdlib decomposition instead numbers off-tour nodes after every on-tour one, in
    // index order, which does make the positions a permutation. That is what to reach for if
    // the wrap rows below ever move into the proof -- the counting argument they would need
    // is a pigeonhole over the positions -- but it costs n rows of n+1 terms where this
    // costs n rows of one, and nothing today buys anything with it.
    for (long i = 0; i < n; ++i)
        model.add_labelled_constraint(
            _constraint_id, "off_pos_" + to_string(i), WPBSum{} + 1_i * data.pos.at(i) <= 0_i, HalfReifyOnConjunctionOf{{_succ[i] == Integer{i}}});

    // How many row families an edge needs depends on whether the wrap edge is known.
    //
    // Anchored, it is: only the edges into the named node wrap, so each edge gets exactly
    // one family, and this is precisely Circuit's shape -- it writes the `+1` form for
    // every column but 0 and the wrap form for column 0, because it anchors on node 0.
    //
    // Unanchored, it is not: the wrap edge is the one into whichever node is `first`, which
    // is only pinned down once the membership literals are, so both cases have to be
    // written and every certificate splits over the candidates. This is the one place where
    // the encoding carries something for the proof's benefit rather than saying the
    // constraint as compactly as it could, so it is worth recording why rather than leaving
    // it to be rediscovered. The wrap rows are what let a propagator that has found a
    // closed cycle *count*: chaining them gives "the tour is no longer than this cycle" in
    // a bounded number of steps (see derive_tour_at_most). Without them the encoding is
    // smaller -- n^2 row families rather than 2n^2, smaller than the stdlib decomposition
    // -- and still exact, because a cycle avoiding the anchor still chains to 0 = k. But
    // then that counting fact has to be derived instead, and deriving it needs "the on-tour
    // positions are exactly 0..L-1", a pigeonhole induction *conditional on the variable
    // L*. So the smaller encoding is not a free reformulation; naming an anchor is the way
    // to get it, and that is what with_required_node() is for.
    for (long i = 0; i < n; ++i)
        for (long j = 0; j < n; ++j) {
            if (i == j)
                continue;

            EdgePosLines lines;
            auto pos_difference = [&]() { return WPBSum{} + 1_i * data.pos.at(j) + -1_i * data.pos.at(i); };
            auto role = to_string(i) + "_" + to_string(j);

            auto wraps_here = data.anchor ? (j == *data.anchor) : true;
            auto steps_here = data.anchor ? (j != *data.anchor) : true;

            if (steps_here) {
                auto guard = HalfReifyOnConjunctionOf{{_succ[i] == Integer{j}}};
                if (! data.anchor)
                    guard.emplace_back(! data.first.at(j));
                auto [le, ge] = model.add_labelled_constraint(
                    _constraint_id, "pos_step_" + role + "_le", "pos_step_" + role + "_ge", pos_difference() == 1_i, guard);
                lines.step_le = le;
                lines.step_ge = ge;
            }

            if (wraps_here) {
                auto wrap = pos_difference();
                for (const auto & term : tour_size.terms)
                    wrap += term;
                auto guard = HalfReifyOnConjunctionOf{{_succ[i] == Integer{j}}};
                if (! data.anchor)
                    guard.emplace_back(data.first.at(j));
                auto [le, ge] =
                    model.add_labelled_constraint(_constraint_id, "pos_wrap_" + role + "_le", "pos_wrap_" + role + "_ge", wrap == 1_i, guard);
                lines.wrap_le = le;
                lines.wrap_ge = ge;
            }

            data.edges[i].emplace(j, lines);
        }
}

auto SubCircuit::install_propagators(Propagators & propagators) -> void
{
    auto prevent = ! std::holds_alternative<Check>(_algorithm);
    auto scc_anchor = std::holds_alternative<gcs::subcircuit::SCC>(_algorithm) ? _anchor : nullopt;
    // Proof lines, not search state: they stay valid at every later node, so the cache
    // deliberately does not backtrack, exactly as circuit_scc.cc's does.
    auto cache = std::make_shared<SCCProofCache>();

    if (_tour_size) {
        // Its own propagator, on its own triggers: this one has to wake on a value being
        // removed, not just on a successor being fixed, because losing its own index from
        // a domain is what puts a node on the tour.
        auto reason_vars = _succ;
        reason_vars.emplace_back(*_tour_size);

        Triggers size_triggers;
        size_triggers.on_change = {_succ.begin(), _succ.end()};
        size_triggers.on_bounds = {*_tour_size};
        propagators.install(
            constraint_id(),
            [succ = _succ, owner = constraint_id(), size = *_tour_size, reason_vars = std::move(reason_vars)](
                const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                propagate_tour_size(succ, owner, size, reason_vars, state, inference, logger);
                return PropagatorState::Enable;
            },
            size_triggers);
    }

    Triggers triggers;
    triggers.on_instantiated = {_succ.begin(), _succ.end()};
    // Reachability shrinks when a value is removed, not only when a successor is fixed, so
    // the SCC arm needs the wider trigger.
    if (scc_anchor)
        triggers.on_change = {_succ.begin(), _succ.end()};
    propagators.install(
        constraint_id(),
        [succ = _succ, owner = constraint_id(), pos_data = std::move(_pos_data), unassigned_handle = _state_handles.unassigned, prevent, scc_anchor,
            cache](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            propagate_subcircuit(succ, owner, pos_data, unassigned_handle, prevent, scc_anchor, cache, state, inference, logger);
            // Deliberately not claiming idempotence, unlike circuit::Prevent: forcing a
            // node to be a self loop fixes a successor, which changes the chain structure
            // this pass walked, and one pass makes no attempt to reach the fixpoint of
            // that cascade. The triggers cover it -- every inference here instantiates a
            // successor, so the propagator is re-woken.
            return PropagatorState::Enable;
        },
        triggers);
}

auto SubCircuit::clone() const -> unique_ptr<Constraint>
{
    auto cloned = make_unique<SubCircuit>(_succ);
    cloned->with_algorithm(_algorithm);
    cloned->with_gac_all_different(_gac_all_different);
    if (_tour_size)
        cloned->with_tour_size(*_tour_size);
    if (_required_node)
        cloned->with_required_node(*_required_node);
    return cloned;
}

auto SubCircuit::constraint_type() const -> string
{
    return "subcircuit";
}

auto SubCircuit::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    vector<SExpr> vars;
    for (const auto & var : _succ)
        vars.push_back(tracker.s_expr_term_of(var));
    // The tour size is a semantic argument, not a tuning knob, so it has to appear here or
    // a .scp round trip would quietly drop it and read back a weaker constraint.
    vector<SExpr> terms{SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(std::move(vars))};
    if (_tour_size)
        terms.push_back(tracker.s_expr_term_of(*_tour_size));
    return SExpr::list(std::move(terms));
}
