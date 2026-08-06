#include <gcs/innards/proofs/lifted_cover_cut.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_scaffolding_scope.hh>
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
using std::ranges::any_of;
using std::ranges::sort;
using std::ranges::unique;

namespace
{
    /// A reified inequality as the proof holds it: the flag, and the two lines
    /// defining it, which every step unwrapping it has to cite.
    struct Reified
    {
        ProofFlag flag;
        ProofLine forward, reverse;
    };

    /// Does the first state say everything the second does? It takes no more of
    /// any resource and allows no less on the cut, so every point in the second
    /// is a point in the first.
    [[nodiscard]] auto covers(const LiftedCoverCutState & state, const LiftedCoverCutState & covered) -> bool
    {
        if (state.profit < covered.profit)
            return false;
        for (size_t row = 0; row < state.weights.size(); ++row)
            if (state.weights[row] > covered.weights[row])
                return false;
        return true;
    }

    /// Drop every state another one already covers, leaving an antichain. The
    /// state carrying the most is never covered, so the bound the last layer
    /// reports does not move --- and every state left is still a tuple some 0/1
    /// point reaches exactly, which is what makes that bound the true optimum
    /// rather than an over-estimate.
    ///
    /// Over one row this is a staircase, and what survives runs strictly upwards
    /// in both coordinates, which is why a layer then holds at most one state
    /// per achievable profit. Over several there is no such shape, and the
    /// budget is what stands in for it.
    auto reduce_to_frontier(LiftedCoverCutLayer & states) -> void
    {
        sort(states);
        states.erase(unique(states).begin(), states.end());

        LiftedCoverCutLayer frontier;
        for (const auto & state : states)
            if (! any_of(states, [&](const LiftedCoverCutState & other) { return other != state && covers(other, state); }))
                frontier.push_back(state);
        states = move(frontier);
    }

    /// The rows that can rule something out: everything else admits every subset
    /// of the members, so no derivation could use it and a weight bound against
    /// it would be a flag per state saying nothing.
    [[nodiscard]] auto binding_rows(const vector<vector<Integer>> & demands, const vector<Integer> & capacities) -> vector<size_t>
    {
        vector<size_t> binding;
        for (size_t row = 0; row < capacities.size(); ++row)
            if (std::accumulate(demands[row].begin(), demands[row].end(), 0_i) > capacities[row])
                binding.push_back(row);
        return binding;
    }

    struct Programme
    {
        vector<LiftedCoverCutLayer> layers;
        bool over_budget = false;
        /// Set when some state's profit reached the ceiling asked about, in
        /// which case the layers are whatever had been built when it did. Since
        /// coefficients are never negative and a state only covers one whose
        /// profit is no larger, such a state has a descendant in every later
        /// layer, so stopping there loses nothing.
        bool reached_ceiling = false;
    };

    /// Run the programme forwards, layer by layer. A state after the first `i`
    /// members is a (weights, profit) tuple reachable by taking some of them; a
    /// successor either leaves the next member out or takes it, and one that
    /// would overrun some capacity is not created, because that row forbids it.
    [[nodiscard]] auto build_programme(const vector<vector<Integer>> & demands, const vector<Integer> & coefficients,
        const vector<Integer> & capacities, Integer profit_ceiling, size_t state_budget) -> Programme
    {
        auto rows = capacities.size();
        Programme programme;
        programme.layers.push_back(LiftedCoverCutLayer{LiftedCoverCutState{vector<Integer>(rows, 0_i), 0_i}});
        size_t states = 1;

        for (size_t member = 0; member < coefficients.size(); ++member) {
            LiftedCoverCutLayer next;
            for (const auto & state : programme.layers.back()) {
                next.push_back(state);

                auto weights = state.weights;
                auto fits = true;
                for (size_t row = 0; row < rows && fits; ++row) {
                    weights[row] += demands[row][member];
                    fits = weights[row] <= capacities[row];
                }
                if (fits)
                    next.push_back(LiftedCoverCutState{move(weights), state.profit + coefficients[member]});
            }

            reduce_to_frontier(next);
            states += next.size();
            if (states > state_budget) {
                programme.over_budget = true;
                return programme;
            }

            programme.reached_ceiling = any_of(next, [&](const LiftedCoverCutState & state) { return state.profit >= profit_ceiling; });
            programme.layers.push_back(move(next));
            if (programme.reached_ceiling)
                return programme;
        }

        return programme;
    }

    /// The most any state in a layer allows on the cut.
    [[nodiscard]] auto largest_profit(const LiftedCoverCutLayer & layer) -> Integer
    {
        auto best = 0_i;
        for (const auto & state : layer)
            best = std::max(best, state.profit);
        return best;
    }

    auto check_shape(const vector<vector<Integer>> & demands, const vector<Integer> & coefficients, const vector<Integer> & capacities) -> void
    {
        if (demands.size() != capacities.size())
            throw ProofError{"a lifted cover cut needs one capacity per row of demands"};
        for (const auto & row : demands)
            if (row.size() != coefficients.size())
                throw ProofError{"a lifted cover cut needs one coefficient per demand"};
    }
}

auto gcs::innards::validate_lifted_cover_cut(const vector<vector<Integer>> & demands, const vector<Integer> & coefficients,
    const vector<Integer> & capacities, Integer rhs, size_t state_budget) -> LiftedCoverCutValidity
{
    check_shape(demands, coefficients, capacities);

    auto binding = binding_rows(demands, capacities);
    vector<vector<Integer>> kept_demands;
    vector<Integer> kept_capacities;
    for (auto row : binding) {
        kept_demands.push_back(demands[row]);
        kept_capacities.push_back(capacities[row]);
    }

    // A state whose profit is above the right-hand side is a point breaking the
    // cut, so there is nothing to gain by carrying on once one appears --- and
    // asking about it here is what keeps a layer to one state per achievable
    // profit below the right-hand side, times whatever the weights need.
    auto programme = build_programme(kept_demands, coefficients, kept_capacities, rhs + 1_i, state_budget);
    if (programme.over_budget)
        return LiftedCoverCutValidity{nullopt, true};
    if (programme.reached_ceiling || largest_profit(programme.layers.back()) > rhs)
        return LiftedCoverCutValidity{nullopt, false};

    return LiftedCoverCutValidity{
        LiftedCoverCut{move(kept_demands), move(kept_capacities), move(binding), coefficients, rhs, move(programme.layers)}, false};
}

auto gcs::innards::lifted_cover_cut_optimum(const vector<vector<Integer>> & demands, const vector<Integer> & coefficients,
    const vector<Integer> & capacities, Integer profit_ceiling, size_t state_budget) -> LiftedCoverCutOptimum
{
    check_shape(demands, coefficients, capacities);

    auto binding = binding_rows(demands, capacities);
    vector<vector<Integer>> kept_demands;
    vector<Integer> kept_capacities;
    for (auto row : binding) {
        kept_demands.push_back(demands[row]);
        kept_capacities.push_back(capacities[row]);
    }

    auto programme = build_programme(kept_demands, coefficients, kept_capacities, profit_ceiling, state_budget);
    if (programme.over_budget)
        return LiftedCoverCutOptimum{nullopt, true};
    if (programme.reached_ceiling)
        return LiftedCoverCutOptimum{nullopt, false};

    return LiftedCoverCutOptimum{largest_profit(programme.layers.back()), false};
}

auto gcs::innards::derive_lifted_cover_cut(ProofLogger & logger, const vector<ProofLine> & capacity_rows, const LiftedCoverCut & cut,
    const vector<ProofFlag> & flags, const vector<Integer> & claimed_coefficients, const vector<vector<ProofFlag>> & weaken_out, Integer claimed_rhs,
    ProofLevel level) -> ProofLine
{
    auto members = flags.size();
    auto rows = cut.capacities.size();
    if (members != claimed_coefficients.size() || members != cut.coefficients.size() || cut.layers.size() != members + 1)
        throw ProofError{"a lifted cover cut needs one flag and one coefficient per member"};
    if (capacity_rows.size() != rows || weaken_out.size() != rows)
        throw ProofError{"a lifted cover cut needs one supplied row and one weakening list per row it kept"};

    WPBSum claimed;
    for (size_t member = 0; member < members; ++member)
        claimed += claimed_coefficients[member] * flags[member];

    // Nothing to derive: the members cannot between them reach the right-hand
    // side, so no 0/1 point can miss it and the resources do not come into it.
    // This is the usual state of affairs at the edges of a derived constraint's
    // window, where too few of its tasks have flags to add up to anything.
    auto total = std::accumulate(cut.coefficients.begin(), cut.coefficients.end(), 0_i);
    if (total <= cut.rhs)
        return logger.emit_rup_proof_line(move(claimed) <= claimed_rhs, level);

    // Only the pin below survives this routine, extension variables included,
    // since deleting a variable's two defining constraints deletes the
    // variable. See ProofScaffoldingScope.
    ProofScaffoldingScope scaffolding{logger};

    const auto & tracker = logger.names_and_ids_tracker();

    // The running sums every state speaks about: what the first so-many members
    // take from each resource, and what they put on the cut.
    vector<vector<WPBSum>> row_prefix(rows, vector<WPBSum>(members + 1));
    vector<WPBSum> cut_prefix(members + 1);
    for (size_t member = 0; member < members; ++member) {
        for (size_t row = 0; row < rows; ++row) {
            row_prefix[row][member + 1] = row_prefix[row][member];
            row_prefix[row][member + 1] += cut.demands[row][member] * flags[member];
        }
        cut_prefix[member + 1] = cut_prefix[member];
        cut_prefix[member + 1] += cut.coefficients[member] * flags[member];
    }

    // One extension variable per half of a state and one for their conjunction.
    // States within a layer share halves wherever they agree on a coordinate,
    // which over one row means a weight is a state's whole identity and over
    // several means the sharing is worth having.
    vector<vector<map<Integer, Reified>>> at_least(rows, vector<map<Integer, Reified>>(members + 1));
    vector<map<Integer, Reified>> at_most(members + 1);
    vector<map<LiftedCoverCutState, Reified>> reached(members + 1);

    for (size_t layer = 0; layer <= members; ++layer)
        for (const auto & state : cut.layers[layer]) {
            WPBSum conjuncts;
            for (size_t row = 0; row < rows; ++row) {
                auto weight = state.weights[row];
                if (! at_least[row][layer].contains(weight)) {
                    auto [flag, forward, reverse] = logger.create_proof_flag_reifying(
                        row_prefix[row][layer] >= weight, format("lccw{}_{}_{}", row, layer, weight.raw_value), ProofLevel::Temporary);
                    at_least[row][layer].emplace(weight, Reified{flag, forward, reverse});
                }
                conjuncts += 1_i * at_least[row][layer].at(weight).flag;
            }

            if (! at_most[layer].contains(state.profit)) {
                auto [flag, forward, reverse] = logger.create_proof_flag_reifying(
                    cut_prefix[layer] <= state.profit, format("lccp{}_{}", layer, state.profit.raw_value), ProofLevel::Temporary);
                at_most[layer].emplace(state.profit, Reified{flag, forward, reverse});
            }
            conjuncts += 1_i * at_most[layer].at(state.profit).flag;

            auto name = format("lccs{}_{}", layer, state.profit.raw_value);
            for (auto weight : state.weights)
                name += format("_{}", weight.raw_value);
            auto [state_flag, state_forward, state_reverse] =
                logger.create_proof_flag_reifying(move(conjuncts) >= Integer{static_cast<long long>(rows) + 1}, name, ProofLevel::Temporary);
            reached[layer].emplace(state, Reified{state_flag, state_forward, state_reverse});
        }

    // The empty prefix takes nothing and carries nothing, so every half of its
    // one state is true of every point --- each half is a bound on an empty sum,
    // so its own reverse reification is a unit --- and the state's reverse
    // reification then forces the flag.
    const auto & empty_prefix = cut.layers[0].front();
    vector<ProofLine> start_hints;
    for (size_t row = 0; row < rows; ++row)
        start_hints.push_back(at_least[row][0].at(empty_prefix.weights[row]).reverse);
    start_hints.push_back(at_most[0].at(empty_prefix.profit).reverse);
    start_hints.push_back(reached[0].at(empty_prefix).reverse);
    auto at_least_one_state =
        logger.emit(RUPProofRule{move(start_hints)}, WPBSum{} + 1_i * reached[0].at(empty_prefix).flag >= 1_i, ProofLevel::Temporary);

    // The state a layer kept in place of one a transition lands on: it takes no
    // more of any resource and allows no less, so an implication into what was
    // landed on is an implication into this.
    auto covering = [&](size_t layer, const LiftedCoverCutState & landed) -> const LiftedCoverCutState & {
        for (const auto & state : cut.layers[layer])
            if (covers(state, landed))
                return state;
        throw ProofError{"a lifted cover cut's dynamic programme dropped a state nothing covers"};
    };

    // One transition: whether or not the layer's member is taken, a point in
    // `from` is a point in `to`. Each half is a `pol` carrying the source's
    // bound onto the successor's, exactly as knapsack_upfront's forward chains
    // do, and the state follows from the halves through the conjunction.
    //
    // Each of those `pol`s leaves a clause one unit propagation away, and that
    // clause used to be emitted --- but the only thing that ever wanted it was
    // the state step below, so it is a hint on that step instead. Every half a
    // transition has is cited, along with the source's forward reification,
    // which is what puts the halves in hand, and the successor's reverse, which
    // is what turns them back into a state. Restricting propagation to those is
    // also what keeps a step's cost independent of how much else is standing.
    auto link = [&](size_t layer, const LiftedCoverCutState & from, const LiftedCoverCutState & to, bool taking) -> ProofLine {
        auto other_branch = taking ? ! flags[layer - 1] : flags[layer - 1];

        vector<ProofLine> hints{reached[layer - 1].at(from).forward};
        auto half = [&](const Reified & from_half, const Reified & to_half) {
            hints.push_back(PolBuilder{}.add(to_half.reverse).add(from_half.forward).saturate().emit(logger, ProofLevel::Temporary));
        };

        for (size_t row = 0; row < rows; ++row)
            half(at_least[row][layer - 1].at(from.weights[row]), at_least[row][layer].at(to.weights[row]));
        half(at_most[layer - 1].at(from.profit), at_most[layer].at(to.profit));
        hints.push_back(reached[layer].at(to).reverse);

        return logger.emit(RUPProofRule{move(hints)},
            WPBSum{} + 1_i * ! reached[layer - 1].at(from).flag + 1_i * other_branch + 1_i * reached[layer].at(to).flag >= 1_i,
            ProofLevel::Temporary);
    };

    for (size_t layer = 1; layer <= members; ++layer) {
        auto member = layer - 1;
        // What the layer's own at-least-one will resolve over: the layer before
        // it was complete, and each of its states has a successor here.
        vector<ProofLine> layer_hints{at_least_one_state};
        for (const auto & from : cut.layers[layer - 1]) {
            const auto & left_out = covering(layer, from);
            vector<ProofLine> successor_hints{link(layer, from, left_out, false)};

            WPBSum successors;
            successors += 1_i * ! reached[layer - 1].at(from).flag;
            successors += 1_i * reached[layer].at(left_out).flag;

            // Which resource, if any, the member overruns from here. Several
            // may; one is a proof.
            auto overrun = optional<size_t>{};
            auto weights = from.weights;
            for (size_t row = 0; row < rows && ! overrun; ++row) {
                weights[row] += cut.demands[row][member];
                if (weights[row] > cut.capacities[row])
                    overrun = row;
            }

            if (! overrun) {
                const auto & taken = covering(layer, LiftedCoverCutState{move(weights), from.profit + cut.coefficients[member]});
                successor_hints.push_back(link(layer, from, taken, true));
                // One state can cover both branches, once there is more than one
                // resource for it to be slack in.
                if (taken != left_out)
                    successors += 1_i * reached[layer].at(taken).flag;
            }
            else {
                // That row rules the member out from here. Weaken it down to
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
                pol.add(capacity_rows[*overrun]).add(at_least[*overrun][layer - 1].at(from.weights[*overrun]).forward);
                for (size_t later = layer; later < members; ++later)
                    pol.weaken(flags[later], tracker);
                for (const auto & flag : weaken_out[*overrun])
                    pol.weaken(flag, tracker);
                // Reaching the source and then taking the member is what that
                // lands on being impossible, so both are cited: the state's
                // forward reification for the weight bound the step consumes,
                // and the step itself for what it rules out. Unit propagation
                // often gets there through the rows in the database instead,
                // but a hinted step is only allowed what it names.
                successor_hints.push_back(reached[layer - 1].at(from).forward);
                successor_hints.push_back(pol.saturate().divide_by(weights[*overrun] - cut.capacities[*overrun]).emit(logger, ProofLevel::Temporary));
            }

            layer_hints.push_back(logger.emit(RUPProofRule{move(successor_hints)}, move(successors) >= 1_i, ProofLevel::Temporary));
        }

        // The layer is complete: whatever the members so far did, one of its
        // states covers it. This resolves over the layer before's, which is why
        // that and every one of this layer's successor steps are cited.
        WPBSum complete;
        for (const auto & state : cut.layers[layer])
            complete += 1_i * reached[layer].at(state).flag;
        at_least_one_state = logger.emit(RUPProofRule{move(layer_hints)}, move(complete) >= 1_i, ProofLevel::Temporary);
    }

    // One flag for the cut itself, so that a final state contradicting it is a
    // clause rather than two linear constraints no unit propagation will put
    // together. Every final state does contradict it, because validate_lifted_
    // cover_cut refused the cut otherwise, so the last layer being complete
    // leaves the flag true.
    auto [holds, holds_forward, holds_reverse] = logger.create_proof_flag_reifying(cut_prefix[members] <= cut.rhs, "lcccut", ProofLevel::Temporary);

    vector<ProofLine> holds_hints{at_least_one_state};
    for (const auto & state : cut.layers[members]) {
        auto against = PolBuilder{}.add(holds_reverse).add(at_most[members].at(state.profit).forward).saturate().emit(logger, ProofLevel::Temporary);
        holds_hints.push_back(logger.emit(RUPProofRule{vector<ProofLine>{reached[members].at(state).forward, against}},
            WPBSum{} + 1_i * holds + 1_i * ! reached[members].at(state).flag >= 1_i, ProofLevel::Temporary));
    }

    auto established = logger.emit(RUPProofRule{move(holds_hints)}, WPBSum{} + 1_i * holds >= 1_i, ProofLevel::Temporary);
    auto derived = PolBuilder{}.add(holds_forward).add(established, total - cut.rhs).emit(logger, ProofLevel::Temporary);

    // Restore the caller's level and pin there, while the scaffolding is still
    // alive for VeriPB to resolve the reference against, then drop it.
    scaffolding.restore();
    return logger.emit(ImpliesProofRule{derived}, move(claimed) <= claimed_rhs, level);
}
