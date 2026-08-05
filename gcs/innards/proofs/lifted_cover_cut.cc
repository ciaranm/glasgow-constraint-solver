#include <gcs/innards/proofs/lifted_cover_cut.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/pseudo_boolean.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
using std::format;
#else
#include <fmt/core.h>
using fmt::format;
#endif

#include <algorithm>
#include <cstddef>
#include <map>
#include <numeric>
#include <optional>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::map;
using std::move;
using std::nullopt;
using std::optional;
using std::size_t;
using std::vector;
using std::ranges::sort;

namespace
{
    /// A reified inequality as the proof holds it: the flag, and the two lines
    /// defining it, which every step unwrapping it has to cite.
    struct Reified
    {
        ProofFlag flag;
        ProofLine forward, reverse;
    };

    /// Drop every state another one already covers. A state taking no more of
    /// the resource while allowing no less on the cut says everything the
    /// covered one does, so the covered one can go --- and the state carrying
    /// the most is never covered, so the bound the last layer reports does not
    /// move. What is left runs strictly upwards in both coordinates, which is
    /// why a layer holds at most one state per achievable profit.
    auto reduce_to_frontier(LiftedCoverCutLayer & states) -> void
    {
        sort(states, [](const LiftedCoverCutState & a, const LiftedCoverCutState & b) {
            if (a.weight != b.weight)
                return a.weight < b.weight;
            return a.profit > b.profit;
        });

        LiftedCoverCutLayer frontier;
        auto covered_up_to = -1_i;
        for (const auto & state : states)
            if (state.profit > covered_up_to) {
                covered_up_to = state.profit;
                frontier.push_back(state);
            }
        states = move(frontier);
    }
}

auto gcs::innards::validate_lifted_cover_cut(const vector<Integer> & demands, const vector<Integer> & coefficients, Integer capacity, Integer rhs)
    -> optional<LiftedCoverCut>
{
    if (demands.size() != coefficients.size())
        throw ProofError{"a lifted cover cut needs one coefficient per demand"};

    vector<LiftedCoverCutLayer> layers{LiftedCoverCutLayer{LiftedCoverCutState{0_i, 0_i}}};
    for (size_t member = 0; member < demands.size(); ++member) {
        LiftedCoverCutLayer next;
        for (const auto & state : layers.back()) {
            // Leaving the member out reaches the same pair one layer on; taking
            // it costs its demand and pays its coefficient, and the row rules it
            // out entirely once that overruns the capacity. That is the only use
            // the row gets, and is what makes the cut a consequence of it.
            next.push_back(state);
            if (state.weight + demands[member] <= capacity)
                next.push_back(LiftedCoverCutState{state.weight + demands[member], state.profit + coefficients[member]});
        }
        reduce_to_frontier(next);
        layers.push_back(move(next));
    }

    // The frontier runs upwards, so the last state of the last layer is the
    // most any 0/1 point the row allows can put on the cut's left-hand side.
    if (layers.back().back().profit > rhs)
        return nullopt;

    return LiftedCoverCut{demands, coefficients, capacity, rhs, move(layers)};
}

auto gcs::innards::derive_lifted_cover_cut(ProofLogger & logger, ProofLine capacity_row, const LiftedCoverCut & cut, const vector<ProofFlag> & flags,
    const vector<Integer> & claimed_coefficients, const vector<ProofFlag> & weaken_out, Integer claimed_rhs, ProofLevel level) -> ProofLine
{
    auto members = flags.size();
    if (members != claimed_coefficients.size() || members != cut.demands.size() || cut.layers.size() != members + 1)
        throw ProofError{"a lifted cover cut needs one flag and one coefficient per member"};

    WPBSum claimed;
    for (size_t member = 0; member < members; ++member)
        claimed += claimed_coefficients[member] * flags[member];

    // Nothing to derive: the members cannot between them reach the right-hand
    // side, so no 0/1 point can miss it and the resource does not come into it.
    // This is the usual state of affairs at the edges of a derived constraint's
    // window, where too few of its tasks have flags to add up to anything.
    auto total = std::accumulate(cut.coefficients.begin(), cut.coefficients.end(), 0_i);
    if (total <= cut.rhs)
        return logger.emit_rup_proof_line(move(claimed) <= claimed_rhs, level);

    // The scaffolding goes one level deeper than the caller's own, so that
    // forgetting it on the way out cannot take the caller's scope with it ---
    // the same isolation recover_am1() needs, and for the same reason: a caller
    // inside a JustifyExplicitly is already using its own Temporary depth. Only
    // the pin below survives this routine, extension variables included, since
    // deleting a variable's two defining constraints deletes the variable.
    auto saved_level = logger.proof_level();
    logger.enter_proof_level(saved_level + 1);

    const auto & tracker = logger.names_and_ids_tracker();

    // The two running sums every state speaks about: what the first so-many
    // members take from the resource, and what they put on the cut.
    vector<WPBSum> row_prefix(members + 1), cut_prefix(members + 1);
    for (size_t member = 0; member < members; ++member) {
        row_prefix[member + 1] = row_prefix[member];
        row_prefix[member + 1] += cut.demands[member] * flags[member];
        cut_prefix[member + 1] = cut_prefix[member];
        cut_prefix[member + 1] += cut.coefficients[member] * flags[member];
    }

    // One extension variable per half of a state and one for their conjunction.
    // A layer's weights and profits are distinct, so a state is keyed by either.
    vector<map<Integer, Reified>> at_least(members + 1), at_most(members + 1);
    vector<map<LiftedCoverCutState, ProofFlag>> reached(members + 1);

    for (size_t layer = 0; layer <= members; ++layer)
        for (const auto & state : cut.layers[layer]) {
            auto [weight_flag, weight_forward, weight_reverse] = logger.create_proof_flag_reifying(
                row_prefix[layer] >= state.weight, format("lccw{}_{}", layer, state.weight.raw_value), ProofLevel::Temporary);
            at_least[layer].emplace(state.weight, Reified{weight_flag, weight_forward, weight_reverse});

            auto [profit_flag, profit_forward, profit_reverse] = logger.create_proof_flag_reifying(
                cut_prefix[layer] <= state.profit, format("lccp{}_{}", layer, state.profit.raw_value), ProofLevel::Temporary);
            at_most[layer].emplace(state.profit, Reified{profit_flag, profit_forward, profit_reverse});

            auto [state_flag, state_forward, state_reverse] =
                logger.create_proof_flag_reifying(WPBSum{} + 1_i * weight_flag + 1_i * profit_flag >= 2_i,
                    format("lccs{}_{}_{}", layer, state.weight.raw_value, state.profit.raw_value), ProofLevel::Temporary);
            reached[layer].emplace(state, state_flag);
            (void)state_forward;
            (void)state_reverse;
        }

    // The empty prefix takes nothing and carries nothing, so both halves of its
    // one state are true of every point and the reifications force the flag.
    logger.emit_rup_proof_line(WPBSum{} + 1_i * reached[0].at(cut.layers[0].front()) >= 1_i, ProofLevel::Temporary);

    // The state a layer kept in place of one a transition lands on: it takes no
    // more of the resource and allows no less, so an implication into what was
    // landed on is an implication into this. The frontier runs upwards, so the
    // first one that qualifies is the one with the tightest profit.
    auto covering = [&](size_t layer, const LiftedCoverCutState & landed) -> const LiftedCoverCutState & {
        for (const auto & state : cut.layers[layer])
            if (state.weight <= landed.weight && state.profit >= landed.profit)
                return state;
        throw ProofError{"a lifted cover cut's dynamic programme dropped a state nothing covers"};
    };

    // One transition: whether or not the layer's member is taken, a point in
    // `from` is a point in `to`. Each half is a `pol` leaving its clause one
    // unit propagation away, exactly as knapsack_upfront's forward chains do,
    // and the state follows from the two through the conjunction.
    auto link = [&](size_t layer, const LiftedCoverCutState & from, const LiftedCoverCutState & to, bool taking) {
        auto other_branch = taking ? ! flags[layer - 1] : flags[layer - 1];
        const auto & from_weight = at_least[layer - 1].at(from.weight);
        const auto & to_weight = at_least[layer].at(to.weight);
        const auto & from_profit = at_most[layer - 1].at(from.profit);
        const auto & to_profit = at_most[layer].at(to.profit);

        PolBuilder{}.add(to_weight.reverse).add(from_weight.forward).saturate().emit(logger, ProofLevel::Temporary);
        logger.emit_rup_proof_line(WPBSum{} + 1_i * ! from_weight.flag + 1_i * other_branch + 1_i * to_weight.flag >= 1_i, ProofLevel::Temporary);

        PolBuilder{}.add(to_profit.reverse).add(from_profit.forward).saturate().emit(logger, ProofLevel::Temporary);
        logger.emit_rup_proof_line(WPBSum{} + 1_i * ! from_profit.flag + 1_i * other_branch + 1_i * to_profit.flag >= 1_i, ProofLevel::Temporary);

        logger.emit_rup_proof_line(
            WPBSum{} + 1_i * ! reached[layer - 1].at(from) + 1_i * other_branch + 1_i * reached[layer].at(to) >= 1_i, ProofLevel::Temporary);
    };

    for (size_t layer = 1; layer <= members; ++layer) {
        auto member = layer - 1;
        for (const auto & from : cut.layers[layer - 1]) {
            const auto & left_out = covering(layer, from);
            link(layer, from, left_out, false);

            WPBSum successors;
            successors += 1_i * ! reached[layer - 1].at(from);
            successors += 1_i * reached[layer].at(left_out);

            auto weight = from.weight + cut.demands[member];
            if (weight <= cut.capacity) {
                const auto & taken = covering(layer, LiftedCoverCutState{weight, from.profit + cut.coefficients[member]});
                link(layer, from, taken, true);
                if (taken != left_out)
                    successors += 1_i * reached[layer].at(taken);
            }
            else {
                // The row rules the member out from here. Weaken it down to
                // this member and the ones the state already accounts for, add
                // what the state says about those --- which cancels them --- and
                // what is left says this member alone would overshoot.
                //
                // The weakening is for the checker's benefit rather than for
                // soundness: every term left in adds its own demand to the
                // degree, and no combination of the literals it leaves behind
                // can cover a degree it raised by more than it can reach, so the
                // member is forced out either way. What it buys is that the step
                // lands on a two-literal clause instead of on something as wide
                // as the donor, which every later unit propagation would pay
                // for. Removing it therefore makes nothing fail, which is why
                // there is no mutation for it.
                PolBuilder pol;
                pol.add(capacity_row).add(at_least[layer - 1].at(from.weight).forward);
                for (size_t later = layer; later < members; ++later)
                    pol.weaken(flags[later], tracker);
                for (const auto & flag : weaken_out)
                    pol.weaken(flag, tracker);
                pol.saturate().divide_by(weight - cut.capacity).emit(logger, ProofLevel::Temporary);
            }

            logger.emit_rup_proof_line(move(successors) >= 1_i, ProofLevel::Temporary);
        }

        // The layer is complete: whatever the members so far did, one of its
        // states covers it. This resolves over the layer before's.
        WPBSum complete;
        for (const auto & state : cut.layers[layer])
            complete += 1_i * reached[layer].at(state);
        logger.emit_rup_proof_line(move(complete) >= 1_i, ProofLevel::Temporary);
    }

    // One flag for the cut itself, so that a final state contradicting it is a
    // clause rather than two linear constraints no unit propagation will put
    // together. Every final state does contradict it, because validate_lifted_
    // cover_cut refused the cut otherwise, so the last layer being complete
    // leaves the flag true.
    auto [holds, holds_forward, holds_reverse] = logger.create_proof_flag_reifying(cut_prefix[members] <= cut.rhs, "lcccut", ProofLevel::Temporary);

    for (const auto & state : cut.layers[members]) {
        PolBuilder{}.add(holds_reverse).add(at_most[members].at(state.profit).forward).saturate().emit(logger, ProofLevel::Temporary);
        logger.emit_rup_proof_line(WPBSum{} + 1_i * holds + 1_i * ! reached[members].at(state) >= 1_i, ProofLevel::Temporary);
    }

    auto established = logger.emit_rup_proof_line(WPBSum{} + 1_i * holds >= 1_i, ProofLevel::Temporary);
    auto derived = PolBuilder{}.add(holds_forward).add(established, total - cut.rhs).emit(logger, ProofLevel::Temporary);

    // Restore the caller's level and pin there, while the scaffolding is still
    // alive for VeriPB to resolve the reference against, then drop it.
    logger.enter_proof_level(saved_level);
    auto result = logger.emit(ImpliesProofRule{derived}, move(claimed) <= claimed_rhs, level);
    logger.forget_proof_level(saved_level + 2);
    return result;
}
