#include <gcs/constraints/cumulative/checkpoint_recovery.hh>
#include <gcs/innards/power.hh>
#include <gcs/innards/proofs/flag_bridge.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>

#include <string>
#include <variant>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_pair;
using std::make_tuple;
using std::nullopt;
using std::optional;
using std::pair;
using std::size_t;
using std::string;
using std::to_string;
using std::vector;

namespace
{
    using Data = ConstraintProofModelData<Cumulative>;

    // One half of a flag's reification, as whatever it takes to cite it: a
    // label where the halves are OPB rows, a line number where they were
    // emitted inside the proof. reification_half is what knows the difference,
    // and #780 step 10 is what makes there be one.
    auto half_of(const NamesAndIDsTracker & tracker, const ProofFlag & flag, ReificationHalf which) -> ProofLine
    {
        return reification_half(tracker, flag, which);
    }

    // The reification coefficient a forward half was emitted with, which is
    // what a pol has to multiply the flag by for the guard terms to cancel
    // rather than leave a residue. Asked rather than assumed, exactly as
    // Disjunctive's sorting-network certificate asks it.
    auto guard_coefficient(NamesAndIDsTracker & tracker, const WPBSumLE & ineq, const ProofFlag & flag) -> Integer
    {
        return -tracker.reification_shape(ineq, HalfReifyOnConjunctionOf{{flag}}).reif_coefficient;
    }

    // The load at `t` as the per-time capacity row states it: a coefficient on
    // the activity flag for a constant height, and the bit-linearised
    // contribution for a variable one.
    //
    // One function because it has two callers who must agree exactly --- the
    // recovery, which derives this row, and the differential check, which
    // asserts the derived row implies the model's. A copy that drifted would
    // make the check compare the recovery against something the model does not
    // say, which is the one failure the check exists to catch and the one it
    // could not report.
    auto per_time_load(const CumulativeInputs & inputs, Integer t) -> WPBSum
    {
        WPBSum load;
        for (auto i : inputs.active_tasks) {
            if (t < inputs.per_task_t_lo[i] || t > inputs.per_task_t_hi[i])
                continue;
            auto idx = (t - inputs.per_task_t_lo[i]).raw_value;
            if (is_constant_variable(inputs.heights[i]))
                load += constant_value_of(inputs.heights[i]) * inputs.active_flags[i][idx];
            else {
                const auto & bits = inputs.contrib_flags[i][idx];
                for (Integer k = 0_i; k.raw_value < static_cast<long long>(bits.size()); ++k)
                    load += power2(k) * bits[k.raw_value];
            }
        }
        return load;
    }

    // And the whole row, in whichever of the two forms the capacity's
    // constancy picks: a number on the right where it is constant, and a
    // (-1)*capacity term on the left where it is not, exactly as the encoder
    // writes it. Shared for the same reason per_time_load is.
    auto per_time_capacity_row(const CumulativeInputs & inputs, Integer t) -> WPBSumLE
    {
        auto load = per_time_load(inputs, t);
        if (is_constant_variable(inputs.capacity))
            return move(load) <= constant_value_of(inputs.capacity);
        load += -1_i * inputs.capacity;
        return move(load) <= 0_i;
    }
}

auto gcs::innards::cumulative_shape_supports_checkpoint_recovery(const vector<size_t> & active_tasks, const vector<optional<IntegerVariableID>> &,
    const vector<IntegerVariableID> &, const vector<IntegerVariableID> &, IntegerVariableID) -> bool
{
    // Every shape the encoder can write is now one the recovery can speak
    // about: an optional task and a variable length through the diagonal, a
    // variable height through the contribution swap, a variable capacity by
    // carrying the capacity as a term the way the encoder does. What is left
    // is the one thing that is not a shape --- a Cumulative with no active
    // task has no checkpoint row to recover from, because the encoding writes
    // them over the active tasks.
    //
    // The presence, length, height and capacity parameters stay in the
    // signature: this is the question "could the recovery speak about a
    // Cumulative of this shape", the answer happens to have stopped depending
    // on them, and a caller should not have to know that.
    return ! active_tasks.empty();
}

auto gcs::innards::cumulative_checkpoint_recovery_applies(const CumulativeInputs & inputs, const ProofLogger & logger) -> bool
{
    if (! cumulative_shape_supports_checkpoint_recovery(inputs.active_tasks, inputs.presence, inputs.lengths, inputs.heights, inputs.capacity))
        return false;
    for (auto i : inputs.active_tasks) {
        // The block has to be in the model to be recovered from. Asking for one
        // task's row is enough: the encoding writes them for every active task
        // or for none.
        if (! logger.names_and_ids_tracker().constraint_row_label(inputs.owner, Data::checkpoint_row_role(i)))
            return false;
        // A variable height's swap is stated over the reification halves of the
        // pair contribution bits, so it needs those bits to *be* reifications:
        // conjunctions with the height's own bits. Where a height has no bits
        // to conjoin with --- a view, or a declared lower bound below zero ---
        // the encoding falls back to linearising the product with three rows
        // per pair, and this declines rather than recovering a row it cannot
        // state.
        if (! is_constant_variable(inputs.heights[i]) && ! inputs.pair_contribution_bits_are_conjunctions)
            return false;
    }
    return true;
}

auto gcs::innards::recover_cumulative_capacity_row(ProofLogger & logger, const CumulativeInputs & inputs, CheckpointRecoveryCache & cache, Integer t)
    -> optional<ProofLine>
{
    if (auto already = cache.recovered.find(t); already != cache.recovered.end())
        return already->second;
    if (! cumulative_checkpoint_recovery_applies(inputs, logger))
        return nullopt;

    auto & tracker = logger.names_and_ids_tracker();

    // The candidates: the tasks the encoding gave a flag at t. Windows differ
    // from task to task, so this is not every active task --- and a task
    // without a flag at t is not in the row being recovered, takes no part in
    // the case split, and has its checkpoint term weakened away below.
    vector<size_t> candidates;
    for (auto i : inputs.active_tasks)
        if (t >= inputs.per_task_t_lo[i] && t <= inputs.per_task_t_hi[i])
            candidates.push_back(i);
    if (candidates.empty())
        return nullopt;

    auto height = [&](size_t i) { return constant_value_of(inputs.heights[i]); };
    auto flag_at = [&](const vector<vector<ProofFlag>> & flags, size_t i) -> const ProofFlag & {
        return flags[i][(t - inputs.per_task_t_lo[i]).raw_value];
    };
    auto cb = [&](size_t i) -> const ProofFlag & { return flag_at(inputs.before_flags, i); };
    auto ca = [&](size_t i) -> const ProofFlag & { return flag_at(inputs.after_flags, i); };
    auto cact = [&](size_t i) -> const ProofFlag & { return flag_at(inputs.active_flags, i); };
    auto pair_flag = [&](const ProofFlagKey & key) { return *tracker.find_proof_flag_values(inputs.owner, key); };
    auto sb = [&](size_t i, size_t j) { return pair_flag(Data::pair_before_flag_key(i, j)); };
    auto sa = [&](size_t i, size_t j) { return pair_flag(Data::pair_after_flag_key(i, j)); };
    auto sact = [&](size_t i, size_t j) { return pair_flag(Data::pair_active_flag_key(i, j)); };
    // The diagonal is the one pair whose activity flag may not exist: `j` is on
    // its own checkpoint row unconditionally when it has a constant length and
    // no presence, and then the encoding folds its height into the right hand
    // side rather than minting a flag to carry it. Where the flag *is* there,
    // `j`'s term is on the row like anyone else's and has to be cancelled like
    // anyone else's. See Data::pair_active_flag_key.
    auto sact_diagonal = [&](size_t j) { return tracker.find_proof_flag_values(inputs.owner, Data::pair_active_flag_key(j, j)); };

    // A variable height is not a coefficient on an activity flag: what is on
    // every capacity row is the bit-linearised contribution, `cc` per (task,
    // time) and `scc` per (task, task). See the encoding.
    auto var_height = [&](size_t i) { return ! is_constant_variable(inputs.heights[i]); };
    auto cc_bits = [&](size_t i) -> const vector<ProofFlag> & { return inputs.contrib_flags[i][(t - inputs.per_task_t_lo[i]).raw_value]; };
    auto scc_bits = [&](size_t i, size_t j) {
        vector<ProofFlag> bits;
        for (Integer k = 0_i;; ++k) {
            auto flag = tracker.find_proof_flag_values(inputs.owner, Data::pair_contribution_flag_key(i, j, k));
            if (! flag)
                break;
            bits.push_back(*flag);
        }
        return bits;
    };
    auto bit_sum = [&](const vector<ProofFlag> & bits) {
        WPBSum sum;
        for (Integer k = 0_i; k.raw_value < static_cast<long long>(bits.size()); ++k)
            sum += power2(k) * bits[k.raw_value];
        return sum;
    };
    auto row = [&](const string & role) { return ProofLine{*tracker.constraint_row_label(inputs.owner, role)}; };

    // The most the candidates could take between them, which is all the
    // trivial-case test below needs.
    Integer total = 0_i;
    for (auto i : candidates) {
        if (var_height(i)) {
            // The most the bits can say, which is all the trivial-case test
            // below needs. Looser than ub(h_i) when the height's range does not
            // fill its bits, which only ever costs a shortcut, never a wrong
            // answer.
            for (Integer k = 0_i; k.raw_value < static_cast<long long>(cc_bits(i).size()); ++k)
                total += power2(k);
        }
        else
            total += height(i);
    }

    // Nothing to argue about: even every candidate at once fits. The row is a
    // tautology over the flags' own bounds, so it needs no checkpoint at all.
    //
    // Only available against a constant capacity: the test is "does the most
    // the candidates can take fit in what the resource supplies", and a
    // variable capacity has no single number to be compared against. It could
    // be asked of the capacity's lower bound, but that bound is not among the
    // recovery's inputs and this is a shortcut rather than a step --- a
    // variable capacity simply takes the long way round, the derivation not
    // caring whether the row it proves happens to be slack.
    if (is_constant_variable(inputs.capacity) && total - constant_value_of(inputs.capacity) <= 0_i) {
        auto trivial = logger.emit_rup_proof_line(per_time_capacity_row(inputs, t), ProofLevel::Top);
        cache.recovered.emplace(t, trivial);
        return trivial;
    }

    // --- the order facts, which say nothing about t and are derived once -----
    //
    // Totality is a theorem here rather than an axiom, which is the one place
    // the start-checkpoint encoding is better off than Disjunctive's: its
    // before flag carries a duration, so its separation clause has to be
    // asserted. sb_{i,j} is starts-only, so the two [f] halves have starts that
    // cancel exactly between them, and what is left divides by two.
    for (size_t a = 0; a < candidates.size(); ++a)
        for (size_t b = a + 1; b < candidates.size(); ++b) {
            auto i = candidates[a], j = candidates[b];
            if (cache.totality.contains(make_pair(i, j)))
                continue;
            PolBuilder pol;
            pol.add(half_of(tracker, sb(i, j), ReificationHalf::ImpliedBy));
            pol.add(half_of(tracker, sb(j, i), ReificationHalf::ImpliedBy));
            cache.totality.emplace(make_pair(i, j), pol.divide_by(2_i).saturate().emit(logger, ProofLevel::Top));
        }

    // Transitivity, one pol per ordered triple, all three starts cancelling.
    // Materialised only for the triples a recovery actually asks for: the pool
    // is cubic, and standing rows are the one cost of this that grows with the
    // task count rather than with what the search touches.
    for (auto a : candidates)
        for (auto b : candidates)
            for (auto c : candidates) {
                if (a == b || b == c || a == c)
                    continue;
                if (cache.transitivity.contains(make_tuple(a, b, c)))
                    continue;
                PolBuilder pol;
                pol.add(half_of(tracker, sb(a, b), ReificationHalf::Implies));
                pol.add(half_of(tracker, sb(b, c), ReificationHalf::Implies));
                pol.add(half_of(tracker, sb(a, c), ReificationHalf::ImpliedBy));
                cache.transitivity.emplace(make_tuple(a, b, c), pol.saturate().emit(logger, ProofLevel::Top));
            }

    // --- ca_{i,t} /\ cb_{j,t} -> sa_{i,j} ------------------------------------
    //
    // If i is still running at t and j has started by t, then i is still
    // running when j starts: s_i + l_i >= t + 1 >= s_j + 1. One pol, with the
    // starts (and, when it is there, the length) cancelling across the three
    // rows and the constants leaving degree one, so saturating gives a clause
    // rather than something at its own degree. This is Disjunctive's
    // emit_before_pol with the flag polarity flipped.
    for (auto i : candidates)
        for (auto j : candidates) {
            if (i == j)
                continue;
            PolBuilder pol;
            pol.add(half_of(tracker, ca(i), ReificationHalf::Implies));
            pol.add(half_of(tracker, cb(j), ReificationHalf::Implies));
            pol.add(half_of(tracker, sa(i, j), ReificationHalf::ImpliedBy));
            pol.saturate().emit(logger, ProofLevel::Top);
        }

    // **No diagonal counterpart, deliberately.** A variable-length task needs
    // `cact_{j,t} -> sact_{j,j}`, which is `s_j <= t` and `s_j + l_j >= t+1`
    // giving `l_j >= 1`, and it is tempting to write the pol above for it with
    // sact_{j,j} standing in for the sa_{j,j} the encoding never mints. It is
    // not needed: the pin below closes on its own, because that fact is about
    // *one* task's variables --- with `l_j <= 0` the sum row pushes `s_j` past
    // `t` and unit propagation has its contradiction. The pol above is needed
    // precisely because its fact is not: it relates `s_i + l_i` to `s_j`, two
    // tasks' starts, and no propagation reaches across them.
    //
    // That is measured, not assumed, and both halves of it: deleting the pol
    // above fails five lanes (derived_cumulative_startcheckpoint, both
    // leak-check lanes, both example encoding lanes), and a diagonal one added
    // beside it changes nothing anywhere. Should a rup ever stall here, it
    // fails loudly at the pin rather than quietly, and this comment says what
    // to write.

    // --- e_{i,j}: i does not stand between j and being the latest starter -----
    std::map<pair<size_t, size_t>, ProofFlag> e;
    for (auto i : candidates)
        for (auto j : candidates) {
            if (i == j)
                continue;
            e.emplace(make_pair(i, j),
                std::get<0>(logger.create_proof_flag_reifying(WPBSum{} + 1_i * ! cb(i) + 1_i * sb(i, j) >= 1_i, "ckpe", ProofLevel::Top)));
        }

    // Lifting e along the order, which is where transitivity earns its place:
    // without these the scan below cannot move its champion.
    for (auto i : candidates)
        for (auto j : candidates)
            for (auto k : candidates) {
                if (i == j || j == k || i == k)
                    continue;
                logger.emit_rup_proof_line(
                    WPBSum{} + 1_i * ! e.at(make_pair(i, j)) + 1_i * ! sb(j, k) + 1_i * e.at(make_pair(i, k)) >= 1_i, ProofLevel::Top);
            }

    // --- the scan ------------------------------------------------------------
    //
    // N_k: none of the first k+1 candidates has started by t.
    // W_{j,k}: j has, and is the latest of the first k+1 to have done so.
    // A_k: one of those two things holds. Carried up one candidate at a time.
    vector<ProofFlag> nothing_yet;
    std::map<pair<size_t, size_t>, ProofFlag> champion;
    for (size_t k = 0; k < candidates.size(); ++k) {
        WPBSum none;
        for (size_t p = 0; p <= k; ++p)
            none += 1_i * ! cb(candidates[p]);
        nothing_yet.push_back(
            std::get<0>(logger.create_proof_flag_reifying(move(none) >= Integer(static_cast<long long>(k) + 1), "ckpn", ProofLevel::Top)));

        for (size_t p = 0; p <= k; ++p) {
            auto j = candidates[p];
            WPBSum latest = WPBSum{} + 1_i * cb(j);
            for (size_t q = 0; q <= k; ++q)
                if (q != p)
                    latest += 1_i * e.at(make_pair(candidates[q], j));
            champion.emplace(make_pair(j, k),
                std::get<0>(logger.create_proof_flag_reifying(move(latest) >= Integer(static_cast<long long>(k) + 1), "ckpw", ProofLevel::Top)));
        }
    }

    auto scan =
        logger.emit_rup_proof_line(WPBSum{} + 1_i * champion.at(make_pair(candidates[0], size_t{0})) + 1_i * nothing_yet[0] >= 1_i, ProofLevel::Top);
    for (size_t k = 0; k + 1 < candidates.size(); ++k) {
        auto next = candidates[k + 1];
        auto & fresh = champion.at(make_pair(next, k + 1));
        PolBuilder pol;
        pol.add(scan);
        for (size_t p = 0; p <= k; ++p) {
            auto j = candidates[p];
            pol.add(logger.emit_rup_proof_line(
                WPBSum{} + 1_i * ! champion.at(make_pair(j, k)) + 1_i * champion.at(make_pair(j, k + 1)) + 1_i * fresh >= 1_i, ProofLevel::Top));
        }
        pol.add(logger.emit_rup_proof_line(WPBSum{} + 1_i * ! nothing_yet[k] + 1_i * fresh + 1_i * nothing_yet[k + 1] >= 1_i, ProofLevel::Top));
        scan = pol.saturate().emit(logger, ProofLevel::Top);
    }
    auto last = candidates.size() - 1;

    // --- literalise the target, so an n-way split over a row stays resolution -
    auto target = per_time_capacity_row(inputs, t);
    auto [target_flag, target_forward, target_reverse] = logger.create_proof_flag_reifying(target, "ckpf", ProofLevel::Top);

    // --- each case implies the target ---------------------------------------
    PolBuilder finish;
    finish.add(scan);
    for (auto j : candidates) {
        auto & w = champion.at(make_pair(j, last));
        vector<ProofLine> pinned;
        for (auto i : candidates)
            if (i != j)
                pinned.push_back(logger.emit_rup_proof_line(WPBSum{} + 1_i * ! w + 1_i * ! cact(i) + 1_i * sact(i, j) >= 1_i, ProofLevel::Top));

        // The diagonal, where the encoding minted a flag for it: `j` active at
        // `t` means `j` is running when `j` starts, which is what sact_{j,j}
        // says. The conjuncts it is defined over are a sub-list of cact_{j,t}'s
        // --- a presence is literally the same atom, and a length is what
        // cb_{j,t} and ca_{j,t} pin between them --- so unit propagation closes
        // it, and no `w` is needed: this one holds whether or not `j` is the
        // latest starter. It is written with the guard anyway, so that the
        // arithmetic below can treat every candidate the same way.
        auto diagonal = sact_diagonal(j);
        optional<ProofLine> diagonal_pin;
        if (diagonal)
            diagonal_pin = logger.emit_rup_proof_line(WPBSum{} + 1_i * ! w + 1_i * ! cact(j) + 1_i * *diagonal >= 1_i, ProofLevel::Top);

        // Tests only: cite the next candidate's checkpoint instead of this
        // one's. Everything still checks --- see RecoverFromWrongCheckpoint.
        auto cite = j;
        if (std::holds_alternative<cumulative_proof_mutation::RecoverFromWrongCheckpoint>(inputs.proof_mutation))
            for (size_t q = 0; q < candidates.size(); ++q)
                if (candidates[q] == j)
                    cite = candidates[(q + 1) % candidates.size()];

        PolBuilder pol;
        pol.add(*tracker.constraint_row_label(inputs.owner, Data::checkpoint_row_role(cite)));
        // A task with no flag at t is not in the row being recovered, so its
        // checkpoint term is dropped rather than pinned. Weakening, while the
        // checkpoint row is still the whole of the running total.
        for (auto i : inputs.active_tasks)
            if (i != j && (t < inputs.per_task_t_lo[i] || t > inputs.per_task_t_hi[i])) {
                if (var_height(i))
                    for (const auto & bit : scc_bits(i, j))
                        pol.weaken(bit, tracker);
                else
                    pol.weaken(sact(i, j), tracker);
            }
        // Swapping each candidate's checkpoint term for its per-time one.
        //
        // A constant height is a coefficient on sact_{i,j}, and the pin cancels
        // it and leaves the same coefficient on ~cact_{i,t}, which is the whole
        // of the conversion: the load term the target's reverse half then
        // cancels against *is* that ~cact term.
        //
        // A variable height is a coefficient on neither. What is on the
        // checkpoint row is the pair's bit-linearised contribution and what is
        // on the target is the per-time one, so the conversion is between two
        // bit sums and the ~cact term is no longer the load --- it is a guard
        // residue, and a residue left on the case clause is a literal the scan
        // cannot resolve away, which comes out as a recovered row weaker than
        // the one asked for. So it has to go, and getting rid of it needs the
        // fact
        //
        //     Sum_k 2^k cc_{i,t,k}  <=  Sum_k 2^k scc_{i,j,k}          (*)
        //
        // *unguarded by cact*, which is true for two different reasons either
        // side of that flag: active at t, and both sides are h_i; not active,
        // and the left is zero while the right is a sum of non-negative terms.
        // Two reasons is a case split, and a case split whose target is a row
        // rather than a clause is relativized on a flag for it --- the same
        // technique, and the same reason for it, as the target row itself a
        // few lines down.
        // A variable height's checkpoint term is a bit sum and so is its
        // per-time one, and swapping them is one `rup` per bit.
        //
        // That is what defining both families as *conjunctions* buys. Bit for
        // bit, cc_{i,t,k} is `cact_{i,t} /\\ bit_k(h_i)` and scc_{i,j,k} is
        // `sact_{i,j} /\\ bit_k(h_i)`, over the same height bit, so
        //
        //     ~w  \\/  ~cc_{i,t,k}  \\/  scc_{i,j,k}
        //
        // closes by unit propagation alone: cc_{i,t,k} gives cact and the
        // height bit, the pin turns cact into sact under w, and sact with that
        // same height bit is scc_{i,j,k}. Summed at 2^k the clauses come to
        //
        //     Sum scc - Sum cc + S.~w >= 0,
        //
        // which cancels the checkpoint row's bits and leaves the per-time ones
        // exactly where a constant height's pin leaves ~cact. Guarded by w
        // alone --- no residue on cact, and so none of the case split this
        // replaced, which existed only because the three-row linearisation put
        // a cact guard on the fact that the two agree.
        //
        // On a flagless diagonal there is no pair bit: the encoding put the
        // height itself on the checkpoint row, and `~cc_{j,t,k} \\/ bit_k(h_j)`
        // --- true with no guard at all, cc being a conjunction that includes
        // that bit --- does the same job.
        auto swap_var_height = [&](size_t i, optional<ProofLine> pin) {
            auto height_var = std::get<SimpleIntegerVariableID>(inputs.heights[i]);
            const auto & cc = cc_bits(i);
            auto pair = pin ? make_optional(scc_bits(i, j)) : optional<vector<ProofFlag>>{};
            for (Integer k = 0_i; k.raw_value < static_cast<long long>(cc.size()); ++k) {
                WPBSum clause;
                if (pin)
                    clause += 1_i * ! w;
                clause += 1_i * ! cc[k.raw_value];
                if (pair)
                    clause += 1_i * (*pair)[k.raw_value];
                else
                    clause += 1_i * ProofBitVariable{height_var, k, true};
                pol.add(logger.emit_rup_proof_line(move(clause) >= 1_i, ProofLevel::Top), power2(k));
            }
        };

        auto swap_term = [&](size_t i, optional<ProofLine> pin) {
            if (var_height(i))
                swap_var_height(i, pin);
            else if (pin)
                pol.add(*pin, height(i));
            else
                pol.add(! cact(i), height(i), tracker);
        };

        size_t p = 0;
        for (auto i : candidates)
            if (i != j)
                swap_term(i, pinned[p++]);
        // And j's own term, by whichever of the two routes the encoding left
        // open. With a flag on the diagonal it cancels exactly as everyone
        // else's does, off the pin above. Without one, the checkpoint row
        // folded j's height into its right hand side, so nothing pins it and
        // nothing cancels against it --- it belongs on the row all the same,
        // j being one of the tasks whose load is being bounded, so it goes on
        // as a literal axiom, which adds the term without moving the degree.
        // Either way what stands now is the target row, guarded by j being the
        // latest starter.
        swap_term(j, diagonal_pin);

        // Turn that into the clause the scan can resolve against, by cancelling
        // the whole load away against the target's own reverse half. The degree
        // that leaves is one, because a reverse half guards at exactly the
        // coefficient that makes its own degree --- so saturating gives a
        // clause and not something at its own degree. If that ever stops being
        // the shape, this fails loudly at the resolution below rather than
        // quietly.
        pol.add(target_reverse);

        // And the guard itself, which the arithmetic above produces only when
        // there was another task to pin: a lone task has no pairwise term, so
        // its case comes out unguarded and would not cancel against the scan.
        // Adding the axiom costs nothing where the term is already there ---
        // saturation flattens the coefficient either way.
        pol.add(! w, tracker);

        finish.add(pol.saturate().emit(logger, ProofLevel::Top));
    }

    // Nobody has started by t, so nobody is active at t and the row holds on
    // the flags' own definitions.
    finish.add(logger.emit_rup_proof_line(WPBSum{} + 1_i * ! nothing_yet[last] + 1_i * target_flag >= 1_i, ProofLevel::Top));
    auto target_holds = finish.saturate().emit(logger, ProofLevel::Top);

    // --- and out from behind the flag ---------------------------------------
    PolBuilder unwrap;
    unwrap.add(target_forward);
    unwrap.add(target_holds, guard_coefficient(tracker, target, target_flag));
    auto recovered = unwrap.emit(logger, ProofLevel::Top);

    cache.recovered.emplace(t, recovered);
    return recovered;
}

auto gcs::innards::check_recovered_cumulative_capacity_rows(ProofLogger & logger, const CumulativeInputs & inputs, CheckpointRecoveryCache & cache)
    -> void
{
    if (! cumulative_checkpoint_recovery_applies(inputs, logger))
        return;

    // Bracketed, so that run_checkpoint_recovery_leak_check.bash can cut the
    // proof here and re-check the prefix against an OPB with no per-time
    // capacity rows in it. That is the only thing that says the recovery is not
    // quietly leaning, through one of its rups, on a row the encoding is about
    // to lose.
    logger.emit_proof_comment("#780 checkpoint recovery begins");
    for (const auto & [t, model_row] : inputs.capacity_lines) {
        auto recovered = recover_cumulative_capacity_row(logger, inputs, cache, t);
        if (! recovered)
            continue;

        logger.emit(ImpliesProofRule{*recovered}, per_time_capacity_row(inputs, t), ProofLevel::Top);
    }
    logger.emit_proof_comment("#780 checkpoint recovery ends");
}
