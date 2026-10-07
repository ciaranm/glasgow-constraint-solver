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

using std::make_optional;
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
    auto per_time_load(ProofLogger & logger, const CumulativeInputs & inputs, Integer t) -> WPBSum
    {
        WPBSum load;
        for (auto i : inputs.active_tasks) {
            if (t < inputs.per_task_t_lo[i] || t > inputs.per_task_t_hi[i])
                continue;
            // As flag_at: the row is stated over flags that may only be defined
            // on demand, and stating it is an ask for them.
            ensure_cumulative_flags_defined(inputs, logger, i, t);
            if (is_constant_variable(inputs.heights[i]))
                load += constant_value_of(inputs.heights[i]) * cumulative_flag(inputs, logger.names_and_ids_tracker(), CumulativeFlag::Active, i, t);
            else {
                auto bits = cumulative_contribution_bits(inputs, logger.names_and_ids_tracker(), i, t);
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
    auto per_time_capacity_row(ProofLogger & logger, const CumulativeInputs & inputs, Integer t) -> WPBSumLE
    {
        auto load = per_time_load(logger, inputs, t);
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
        // A variable height's swap trades a pair contribution bit for a
        // per-time one, one `rup` per bit, and that closes by unit propagation
        // only because *both* families are conjunctions with the height's own
        // bits. Either side linearised the long way breaks it: from
        // `Sum 2^k cc_k <= h` guarded by cact, unit propagation cannot get
        // bit_k(h) out of cc_k, so the clause stalls and veripb rejects the
        // proof rather than the recovery declining to write one.
        //
        // The two conditions are separate because the two families are. A
        // height with no citable bits --- a view, or a declared lower bound
        // below zero --- linearises on both sides. And the per-time family is
        // linearised in the *model* under every encoding but StartCheckpoint,
        // because O(n x horizon) conjunctions would cost more rows than they
        // save; only StartCheckpoint's lazy in-proof minting states them as
        // conjunctions. So `both-recovering` over a variable height is declined
        // here, and gets its variable-height coverage from the
        // `_startcheckpoint` arm instead.
        if (! is_constant_variable(inputs.heights[i]) &&
            ! (inputs.pair_contribution_bits_are_conjunctions && inputs.per_time_contribution_bits_are_conjunctions))
            return false;
    }
    return true;
}

namespace
{
    // What a recovery speaks about, at whatever time point it is asked: the
    // per-(task, time) flags, the pair flags, and the heights. A recovery by
    // chain asks about two time points, which is why the time is a parameter
    // and not part of the object.
    struct Vocabulary
    {
        ProofLogger & logger;
        const CumulativeInputs & inputs;
        NamesAndIDsTracker & tracker;

        [[nodiscard]] auto in_window(size_t i, Integer u) const -> bool
        {
            return u >= inputs.per_task_t_lo[i] && u <= inputs.per_task_t_hi[i];
        }

        // The tasks the encoding gave a flag at u. Windows differ from task to
        // task, so this is not every active task --- and a task without a flag
        // at u is not in the row being recovered, takes no part in a case
        // split, and has its checkpoint term weakened away.
        [[nodiscard]] auto candidates(Integer u) const -> vector<size_t>
        {
            vector<size_t> result;
            for (auto i : inputs.active_tasks)
                if (in_window(i, u))
                    result.push_back(i);
            return result;
        }

        // #780 step 10: the per-(task, time) flags may only be *defined* on
        // demand, so asking for one at `u` asks for its definition first.
        // Nothing happens where the constraint published no definer, which is
        // every encoding whose flags are OPB rows. Every use goes through here.
        auto flag(CumulativeFlag which, size_t i, Integer u) -> ProofFlag
        {
            ensure_cumulative_flags_defined(inputs, logger, i, u);
            return cumulative_flag(inputs, tracker, which, i, u);
        }
        auto cb(size_t i, Integer u) -> ProofFlag
        {
            return flag(CumulativeFlag::Before, i, u);
        }
        auto ca(size_t i, Integer u) -> ProofFlag
        {
            return flag(CumulativeFlag::After, i, u);
        }
        auto cact(size_t i, Integer u) -> ProofFlag
        {
            return flag(CumulativeFlag::Active, i, u);
        }

        [[nodiscard]] auto pair_flag(const ProofFlagKey & key) const -> ProofFlag
        {
            return *tracker.find_proof_flag(inputs.owner, key);
        }
        [[nodiscard]] auto sb(size_t i, size_t j) const -> ProofFlag
        {
            return pair_flag(Data::pair_before_flag_key(i, j));
        }
        [[nodiscard]] auto sa(size_t i, size_t j) const -> ProofFlag
        {
            return pair_flag(Data::pair_after_flag_key(i, j));
        }
        [[nodiscard]] auto sact(size_t i, size_t j) const -> ProofFlag
        {
            return pair_flag(Data::pair_active_flag_key(i, j));
        }

        // The diagonal is the one pair whose activity flag may not exist: `j`
        // is on its own checkpoint row unconditionally when it has a constant
        // length and no presence, and then the encoding folds its height into
        // the right hand side rather than minting a flag to carry it. Where the
        // flag *is* there, `j`'s term is on the row like anyone else's and has
        // to be cancelled like anyone else's. See Data::pair_active_flag_key.
        [[nodiscard]] auto sact_diagonal(size_t j) const -> optional<ProofFlag>
        {
            return tracker.find_proof_flag(inputs.owner, Data::pair_active_flag_key(j, j));
        }

        // A variable height is not a coefficient on an activity flag: what is
        // on every capacity row is the bit-linearised contribution, `cc` per
        // (task, time) and `scc` per (task, task). See the encoding.
        [[nodiscard]] auto var_height(size_t i) const -> bool
        {
            return ! is_constant_variable(inputs.heights[i]);
        }
        [[nodiscard]] auto height(size_t i) const -> Integer
        {
            return constant_value_of(inputs.heights[i]);
        }
        auto cc_bits(size_t i, Integer u) -> vector<ProofFlag>
        {
            ensure_cumulative_flags_defined(inputs, logger, i, u);
            return cumulative_contribution_bits(inputs, tracker, i, u);
        }
        [[nodiscard]] auto scc_bits(size_t i, size_t j) const -> vector<ProofFlag>
        {
            vector<ProofFlag> bits;
            for (Integer k = 0_i;; ++k) {
                auto flag = tracker.find_proof_flag(inputs.owner, Data::pair_contribution_flag_key(i, j, k));
                if (! flag)
                    break;
                bits.push_back(*flag);
            }
            return bits;
        }

        // The most task i can put on a row: its height, or for a variable
        // height the most its bits can say. Looser than ub(h_i) when the
        // height's range does not fill its bits, which only ever costs a
        // shortcut, never a wrong answer. Also exactly the total coefficient
        // the chain's pins put on a task's guard, which is what it is used for
        // there.
        auto most(size_t i, Integer u) -> Integer
        {
            if (! var_height(i))
                return height(i);
            Integer total = 0_i;
            for (Integer k = 0_i; k.raw_value < static_cast<long long>(cc_bits(i, u).size()); ++k)
                total += power2(k);
            return total;
        }
    };

    // Nothing to argue about: even every candidate at once fits. The row is a
    // tautology over the flags' own bounds, so it needs no checkpoint at all.
    //
    // Only available against a constant capacity: the test is "does the most
    // the candidates can take fit in what the resource supplies", and a
    // variable capacity has no single number to be compared against. It could
    // be asked of the capacity's lower bound, but that bound is not among the
    // recovery's inputs and this is a shortcut rather than a step --- a variable
    // capacity simply takes the long way round, the derivation not caring
    // whether the row it proves happens to be slack.
    auto trivially_fits(Vocabulary & v, const vector<size_t> & candidates, Integer t) -> bool
    {
        if (! is_constant_variable(v.inputs.capacity))
            return false;
        Integer total = 0_i;
        for (auto i : candidates)
            total += v.most(i, t);
        return total - constant_value_of(v.inputs.capacity) <= 0_i;
    }

    // One case of a split: j's checkpoint row, with every candidate's term
    // swapped for its per-time one under `guard`, closed against the target's
    // reverse half. Comes out as the clause `~guard \/ target`.
    //
    // `pinned` holds, for each candidate i other than j, the line
    // `~guard \/ ~cact_{i,t} \/ sact_{i,j}`; `diagonal_pin` the same for j
    // itself where the encoding minted sact_{j,j}. What the guard *is* --- j
    // being the latest starter by t, or j starting at exactly t --- is the
    // caller's business: the arithmetic here is the same either way.
    auto emit_case(Vocabulary & v, Integer t, const vector<size_t> & candidates, size_t j, ProofFlag guard,
        const std::map<size_t, ProofLine> & pinned, const optional<ProofLine> & diagonal_pin, ProofLine target_reverse) -> ProofLine
    {
        const auto & inputs = v.inputs;
        auto & tracker = v.tracker;

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
            if (i != j && ! v.in_window(i, t)) {
                if (v.var_height(i))
                    for (const auto & bit : v.scc_bits(i, j))
                        pol.weaken(bit, tracker);
                else
                    pol.weaken(v.sact(i, j), tracker);
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
        // bit sums, and it is one `rup` per bit. That is what defining both
        // families as *conjunctions* buys. Bit for bit, cc_{i,t,k} is
        // `cact_{i,t} /\ bit_k(h_i)` and scc_{i,j,k} is `sact_{i,j} /\
        // bit_k(h_i)`, over the same height bit, so
        //
        //     ~guard  \/  ~cc_{i,t,k}  \/  scc_{i,j,k}
        //
        // closes by unit propagation alone: cc_{i,t,k} gives cact and the
        // height bit, the pin turns cact into sact under the guard, and sact
        // with that same height bit is scc_{i,j,k}. Summed at 2^k the clauses
        // come to
        //
        //     Sum scc - Sum cc + S.~guard >= 0,
        //
        // which cancels the checkpoint row's bits and leaves the per-time ones
        // exactly where a constant height's pin leaves ~cact. Guarded by the
        // guard alone, with no residue on cact: a residue left on the case
        // clause would be a literal the split cannot resolve away.
        //
        // On a flagless diagonal there is no pair bit: the encoding put the
        // height itself on the checkpoint row, and `~cc_{j,t,k} \/ bit_k(h_j)`
        // --- true with no guard at all, cc being a conjunction that includes
        // that bit --- does the same job.
        auto swap_var_height = [&](size_t i, const optional<ProofLine> & pin) {
            auto height_var = std::get<SimpleIntegerVariableID>(inputs.heights[i]);
            auto cc = v.cc_bits(i, t);
            auto pair = pin ? make_optional(v.scc_bits(i, j)) : optional<vector<ProofFlag>>{};
            for (Integer k = 0_i; k.raw_value < static_cast<long long>(cc.size()); ++k) {
                WPBSum clause;
                if (pin)
                    clause += 1_i * ! guard;
                clause += 1_i * ! cc[k.raw_value];
                if (pair)
                    clause += 1_i * (*pair)[k.raw_value];
                else
                    clause += 1_i * ProofBitVariable{height_var, k, true};
                pol.add(v.logger.emit_rup_proof_line(move(clause) >= 1_i, ProofLevel::Top), power2(k));
            }
        };

        auto swap_term = [&](size_t i, const optional<ProofLine> & pin) {
            if (v.var_height(i))
                swap_var_height(i, pin);
            else if (pin)
                pol.add(*pin, v.height(i));
            else
                pol.add(! v.cact(i, t), v.height(i), tracker);
        };

        for (auto i : candidates)
            if (i != j)
                swap_term(i, pinned.at(i));
        // And j's own term, by whichever of the two routes the encoding left
        // open. With a flag on the diagonal it cancels exactly as everyone
        // else's does, off the pin. Without one, the checkpoint row folded j's
        // height into its right hand side, so nothing pins it and nothing
        // cancels against it --- it belongs on the row all the same, j being
        // one of the tasks whose load is being bounded, so it goes on as a
        // literal axiom, which adds the term without moving the degree. Either
        // way what stands now is the target row, under the guard.
        swap_term(j, diagonal_pin);

        // Turn that into the clause the split can resolve against, by
        // cancelling the whole load away against the target's own reverse half.
        // The degree that leaves is one, because a reverse half guards at
        // exactly the coefficient that makes its own degree --- so saturating
        // gives a clause and not something at its own degree.
        pol.add(target_reverse);

        // And the guard itself, which the arithmetic above produces only when
        // there was another task to pin: a lone task has no pairwise term, so
        // its case comes out unguarded and would not cancel against the split.
        // Adding the axiom costs nothing where the term is already there ---
        // saturation flattens the coefficient either way.
        pol.add(! guard, tracker);

        return pol.saturate().emit(v.logger, ProofLevel::Top);
    }

    // The target row literalised, so an n-way split over a row stays
    // resolution: the flag, `flag -> row`, and `row -> flag`.
    auto literalise_target(Vocabulary & v, Integer t) -> std::tuple<ProofFlag, ProofLine, ProofLine, WPBSumLE>
    {
        auto target = per_time_capacity_row(v.logger, v.inputs, t);
        auto [flag, forward, reverse] = v.logger.create_proof_flag_reifying(target, "ckpf", ProofLevel::Top);
        return {flag, forward, reverse, target};
    }

    // And out from behind the flag.
    auto unwrap_target(Vocabulary & v, const WPBSumLE & target, ProofFlag flag, ProofLine forward, ProofLine holds) -> ProofLine
    {
        PolBuilder unwrap;
        unwrap.add(forward);
        unwrap.add(holds, guard_coefficient(v.tracker, target, flag));
        return unwrap.emit(v.logger, ProofLevel::Top);
    }

    // The recovery from nothing: a case split on which candidate is the latest
    // to have started by t. See recover_cumulative_capacity_row's header for
    // the argument. Cubic in the candidates, which is why it is now the
    // fallback: recover_by_chain does a time point in quadratic, given the one
    // before it.
    auto recover_by_scan(Vocabulary & v, CheckpointRecoveryCache & cache, Integer t, const vector<size_t> & candidates) -> ProofLine
    {
        auto & logger = v.logger;
        auto & tracker = v.tracker;
        logger.emit_proof_comment("checkpoint recovery by scan t=" + t.to_string() + " m=" + std::to_string(candidates.size()));

        // --- the order facts, which say nothing about t and are derived once -
        //
        // Totality is a theorem here rather than an axiom, which is the one
        // place the start-checkpoint encoding is better off than Disjunctive's:
        // its before flag carries a duration, so its separation clause has to
        // be asserted. sb_{i,j} is starts-only, so the two [f] halves have
        // starts that cancel exactly between them, and what is left divides by
        // two.
        for (size_t a = 0; a < candidates.size(); ++a)
            for (size_t b = a + 1; b < candidates.size(); ++b) {
                auto i = candidates[a], j = candidates[b];
                if (cache.totality.contains(make_pair(i, j)))
                    continue;
                PolBuilder pol;
                pol.add(half_of(tracker, v.sb(i, j), ReificationHalf::ImpliedBy));
                pol.add(half_of(tracker, v.sb(j, i), ReificationHalf::ImpliedBy));
                cache.totality.emplace(make_pair(i, j), pol.divide_by(2_i).saturate().emit(logger, ProofLevel::Top));
            }

        // Transitivity, one pol per ordered triple, all three starts
        // cancelling. Materialised only for the triples a recovery actually
        // asks for: the pool is cubic, and standing rows are the one cost of
        // this that grows with the task count rather than with what the search
        // touches.
        for (auto a : candidates)
            for (auto b : candidates)
                for (auto c : candidates) {
                    if (a == b || b == c || a == c)
                        continue;
                    if (cache.transitivity.contains(make_tuple(a, b, c)))
                        continue;
                    PolBuilder pol;
                    pol.add(half_of(tracker, v.sb(a, b), ReificationHalf::Implies));
                    pol.add(half_of(tracker, v.sb(b, c), ReificationHalf::Implies));
                    pol.add(half_of(tracker, v.sb(a, c), ReificationHalf::ImpliedBy));
                    cache.transitivity.emplace(make_tuple(a, b, c), pol.saturate().emit(logger, ProofLevel::Top));
                }

        // --- ca_{i,t} /\ cb_{j,t} -> sa_{i,j} ----------------------------------
        //
        // If i is still running at t and j has started by t, then i is still
        // running when j starts: s_i + l_i >= t + 1 >= s_j + 1. One pol, with
        // the starts (and, when it is there, the length) cancelling across the
        // three rows and the constants leaving degree one, so saturating gives
        // a clause rather than something at its own degree. This is
        // Disjunctive's emit_before_pol with the flag polarity flipped.
        for (auto i : candidates)
            for (auto j : candidates) {
                if (i == j)
                    continue;
                PolBuilder pol;
                pol.add(half_of(tracker, v.ca(i, t), ReificationHalf::Implies));
                pol.add(half_of(tracker, v.cb(j, t), ReificationHalf::Implies));
                pol.add(half_of(tracker, v.sa(i, j), ReificationHalf::ImpliedBy));
                pol.saturate().emit(logger, ProofLevel::Top);
            }

        // **No diagonal counterpart, deliberately.** A variable-length task
        // needs `cact_{j,t} -> sact_{j,j}`, which is `s_j <= t` and
        // `s_j + l_j >= t+1` giving `l_j >= 1`, and it is tempting to write the
        // pol above for it with sact_{j,j} standing in for the sa_{j,j} the
        // encoding never mints. It is not needed: the pin below closes on its
        // own, because that fact is about *one* task's variables --- with
        // `l_j <= 0` the sum row pushes `s_j` past `t` and unit propagation has
        // its contradiction. The pol above is needed precisely because its fact
        // is not: it relates `s_i + l_i` to `s_j`, two tasks' starts, and no
        // propagation reaches across them.
        //
        // That is measured, not assumed, and both halves of it: deleting the
        // pol above fails five lanes (derived_cumulative_startcheckpoint, both
        // leak-check lanes, both example encoding lanes), and a diagonal one
        // added beside it changes nothing anywhere. Should a rup ever stall
        // here, it fails loudly at the pin rather than quietly, and this
        // comment says what to write.

        // --- e_{i,j}: i does not stand between j and being the latest starter -
        std::map<pair<size_t, size_t>, ProofFlag> e;
        for (auto i : candidates)
            for (auto j : candidates) {
                if (i == j)
                    continue;
                e.emplace(make_pair(i, j),
                    std::get<0>(logger.create_proof_flag_reifying(WPBSum{} + 1_i * ! v.cb(i, t) + 1_i * v.sb(i, j) >= 1_i, "ckpe", ProofLevel::Top)));
            }

        // Lifting e along the order, which is where transitivity earns its
        // place: without these the scan below cannot move its champion.
        for (auto i : candidates)
            for (auto j : candidates)
                for (auto k : candidates) {
                    if (i == j || j == k || i == k)
                        continue;
                    logger.emit_rup_proof_line(
                        WPBSum{} + 1_i * ! e.at(make_pair(i, j)) + 1_i * ! v.sb(j, k) + 1_i * e.at(make_pair(i, k)) >= 1_i, ProofLevel::Top);
                }

        // --- the scan ----------------------------------------------------------
        //
        // N_k: none of the first k+1 candidates has started by t.
        // W_{j,k}: j has, and is the latest of the first k+1 to have done so.
        // A_k: one of those two things holds. Carried up one candidate at a
        // time.
        vector<ProofFlag> nothing_yet;
        std::map<pair<size_t, size_t>, ProofFlag> champion;
        for (size_t k = 0; k < candidates.size(); ++k) {
            WPBSum none;
            for (size_t p = 0; p <= k; ++p)
                none += 1_i * ! v.cb(candidates[p], t);
            nothing_yet.push_back(
                std::get<0>(logger.create_proof_flag_reifying(move(none) >= Integer(static_cast<long long>(k) + 1), "ckpn", ProofLevel::Top)));

            for (size_t p = 0; p <= k; ++p) {
                auto j = candidates[p];
                WPBSum latest = WPBSum{} + 1_i * v.cb(j, t);
                for (size_t q = 0; q <= k; ++q)
                    if (q != p)
                        latest += 1_i * e.at(make_pair(candidates[q], j));
                champion.emplace(make_pair(j, k),
                    std::get<0>(logger.create_proof_flag_reifying(move(latest) >= Integer(static_cast<long long>(k) + 1), "ckpw", ProofLevel::Top)));
            }
        }

        auto scan = logger.emit_rup_proof_line(
            WPBSum{} + 1_i * champion.at(make_pair(candidates[0], size_t{0})) + 1_i * nothing_yet[0] >= 1_i, ProofLevel::Top);
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

        auto [target_flag, target_forward, target_reverse, target] = literalise_target(v, t);

        // --- each case implies the target -------------------------------------
        PolBuilder finish;
        finish.add(scan);
        for (auto j : candidates) {
            auto w = champion.at(make_pair(j, last));
            std::map<size_t, ProofLine> pinned;
            for (auto i : candidates)
                if (i != j)
                    pinned.emplace(
                        i, logger.emit_rup_proof_line(WPBSum{} + 1_i * ! w + 1_i * ! v.cact(i, t) + 1_i * v.sact(i, j) >= 1_i, ProofLevel::Top));

            // The diagonal, where the encoding minted a flag for it: `j` active
            // at `t` means `j` is running when `j` starts, which is what
            // sact_{j,j} says. The conjuncts it is defined over are a sub-list
            // of cact_{j,t}'s --- a presence is literally the same atom, and a
            // length is what cb_{j,t} and ca_{j,t} pin between them --- so unit
            // propagation closes it, and no `w` is needed: this one holds
            // whether or not `j` is the latest starter. It is written with the
            // guard anyway, so that the arithmetic can treat every candidate the
            // same way.
            optional<ProofLine> diagonal_pin;
            if (auto diagonal = v.sact_diagonal(j))
                diagonal_pin = logger.emit_rup_proof_line(WPBSum{} + 1_i * ! w + 1_i * ! v.cact(j, t) + 1_i * *diagonal >= 1_i, ProofLevel::Top);

            finish.add(emit_case(v, t, candidates, j, w, pinned, diagonal_pin, target_reverse));
        }

        // Nobody has started by t, so nobody is active at t and the row holds
        // on the flags' own definitions.
        finish.add(logger.emit_rup_proof_line(WPBSum{} + 1_i * ! nothing_yet[last] + 1_i * target_flag >= 1_i, ProofLevel::Top));
        auto target_holds = finish.saturate().emit(logger, ProofLevel::Top);

        return unwrap_target(v, target, target_flag, target_forward, target_holds);
    }

    // The recovery from the time point before (#1254): case split on which
    // candidate, if any, starts at exactly t.
    //
    // If none does, every task active at t was active at t - 1, so the load at
    // t is at most the load at t - 1, which `previous` bounds. If j does, every
    // task active at t is active when j starts, so j's checkpoint row bounds
    // the load at t, exactly as the scan's case for j does. The second half is
    // the scan's argument with "j is the latest starter by t" replaced by "j
    // starts at t", which is stronger and so needs no order facts at all: no
    // totality, no transitivity, no champions. What is left is quadratic.
    //
    // `previous` is the row for t - 1, or nullopt where no task can be active
    // at t - 1 --- the base of a chain, where the load before t is nothing.
    // That case needs `0 <= capacity`, so the caller only asks for it against a
    // constant capacity that is not negative.
    //
    // Nullopt where a task's window opens at t and its start has no boundary
    // pin to say it cannot start earlier; the caller falls back to the scan.
    auto recover_by_chain(Vocabulary & v, Integer t, const vector<size_t> & candidates, const optional<ProofLine> & previous) -> optional<ProofLine>
    {
        auto & logger = v.logger;
        auto & tracker = v.tracker;
        const auto & inputs = v.inputs;
        auto had_window_before = [&](size_t i) { return v.in_window(i, t - 1_i); };

        // A task whose window opens at t has no cb_{j,t-1} to say it starts no
        // earlier than t; its declared lower bound says so instead, through
        // the order literal `s_j >= t` and the boundary pin that makes that
        // literal a unit. Gathered first, so that a task without one declines
        // the whole step before anything is written.
        std::map<size_t, ProofLine> opening_rows, opening_pins;
        for (auto j : candidates) {
            if (had_window_before(j))
                continue;
            auto simple = std::get_if<SimpleIntegerVariableID>(&inputs.starts[j]);
            if (! simple)
                return nullopt;
            auto item = tracker.need_pol_item_defining_literal(inputs.starts[j] >= t);
            auto row = std::get_if<ProofLine>(&item);
            auto pin = row ? tracker.boundary_pin_line(*simple, t) : nullopt;
            if (! pin)
                return nullopt;
            opening_rows.emplace(j, *row);
            opening_pins.emplace(j, *pin);
        }

        logger.emit_proof_comment(
            "checkpoint recovery by chain t=" + t.to_string() + " m=" + std::to_string(candidates.size()) + (previous ? "" : " base"));

        auto [target_flag, target_forward, target_reverse, target] = literalise_target(v, t);

        // --- starts_at_i: s_i = t ----------------------------------------------
        //
        // A flag over cb_{i,t} and ~cb_{i,t-1}. Where i's window opens at t its
        // start cannot be below t anyway, and cb_{i,t} alone says it.
        auto started_by = std::holds_alternative<cumulative_proof_mutation::ChainGuardOnStartedBy>(inputs.proof_mutation);
        std::map<size_t, ProofFlag> starts_at;
        std::map<size_t, ProofLine> starts_at_forward, starts_at_reverse;
        for (auto i : candidates) {
            if (had_window_before(i) && ! started_by) {
                auto [flag, forward, reverse] =
                    logger.create_proof_flag_reifying(WPBSum{} + 1_i * v.cb(i, t) + 1_i * ! v.cb(i, t - 1_i) >= 2_i, "ckps", ProofLevel::Top);
                starts_at.emplace(i, flag);
                starts_at_forward.emplace(i, forward);
                starts_at_reverse.emplace(i, reverse);
            }
            else
                starts_at.emplace(i, v.cb(i, t));
        }

        // --- nobody starts at t ------------------------------------------------
        //
        // Each candidate's term at t is at most its term at t - 1, unless it
        // starts at t: `~cact_{i,t} \/ cact_{i,t-1} \/ starts_at_i`, one `rup`
        // given that still running at t means still running at t - 1, which
        // relates `s_i + l_i` to two constants and so is a flag bridge. Summed
        // with the previous row and the target's reverse half, the loads cancel
        // and what is left is
        //
        //     Sum_i h_i starts_at_i + K target >= D,
        //
        // where D is one in a chain and C + 1 at the base, there being no
        // previous row to take C off the degree.
        PolBuilder no_start;
        if (previous && ! std::holds_alternative<cumulative_proof_mutation::ChainDropPreviousRow>(inputs.proof_mutation)) {
            no_start.add(*previous);
            // A task in the previous row whose window has closed by t is not in
            // the row being recovered: weakened away.
            for (auto i : inputs.active_tasks)
                if (had_window_before(i) && ! v.in_window(i, t)) {
                    if (v.var_height(i))
                        for (const auto & bit : v.cc_bits(i, t - 1_i))
                            no_start.weaken(bit, tracker);
                    else
                        no_start.weaken(v.cact(i, t - 1_i), tracker);
                }
        }
        std::map<size_t, Integer> coefficient;
        for (auto i : candidates) {
            auto continues = had_window_before(i);
            optional<ProofLine> still_running;
            if (continues)
                still_running = recover_flag_bridge(logger, v.ca(i, t), v.ca(i, t - 1_i), ProofLevel::Top);
            if (v.var_height(i)) {
                auto now = v.cc_bits(i, t);
                auto before = continues ? v.cc_bits(i, t - 1_i) : vector<ProofFlag>{};
                for (Integer k = 0_i; k.raw_value < static_cast<long long>(now.size()); ++k) {
                    WPBSum clause = WPBSum{} + 1_i * ! now[k.raw_value] + 1_i * starts_at.at(i);
                    if (continues)
                        clause += 1_i * before[k.raw_value];
                    no_start.add(logger.emit_rup_proof_line(move(clause) >= 1_i, ProofLevel::Top), power2(k));
                }
            }
            else if (continues && starts_at_reverse.contains(i)) {
                // As a pol, for the reason the case pins are one: cact_{i,t}'s
                // forward half, starts_at_i's reverse half, the bridge and
                // cact_{i,t-1}'s reverse half cancel cb_{i,t}, cb_{i,t-1},
                // ca_{i,t}, ca_{i,t-1} and the presence pairwise and leave
                // degree one. The bridge comes out saturated at degree two
                // (its thresholds differ by one, plus one), so it is halved
                // first, which leaves it a unit-coefficient clause.
                PolBuilder pin;
                pin.add(*still_running).divide_by(2_i);
                pin.add(half_of(tracker, v.cact(i, t), ReificationHalf::Implies));
                pin.add(starts_at_reverse.at(i));
                pin.add(half_of(tracker, v.cact(i, t - 1_i), ReificationHalf::ImpliedBy));
                no_start.add(pin.saturate().emit(logger, ProofLevel::Top), v.height(i));
            }
            else {
                // A window opening at t, once per task: `cact_{i,t} -> cb_{i,t}`
                // is one of cact's own conjuncts.
                WPBSum clause = WPBSum{} + 1_i * ! v.cact(i, t) + 1_i * starts_at.at(i);
                if (continues)
                    clause += 1_i * v.cact(i, t - 1_i);
                no_start.add(logger.emit_rup_proof_line(move(clause) >= 1_i, ProofLevel::Top), v.height(i));
            }
            coefficient.emplace(i, v.most(i, t));
        }
        no_start.add(target_reverse);
        auto nobody = no_start.emit(logger, ProofLevel::Top);

        // --- j starts at t -----------------------------------------------------
        //
        // Every candidate i active at t is active when j starts. That is
        // sb_{i,j} and sa_{i,j}, each relating two tasks' starts, so each is a
        // pol rather than something unit propagation reaches:
        //
        //     ~cb_{i,t} \/ cb_{j,t-1} \/ sb_{i,j}      s_i <= t <= s_j
        //     ~ca_{i,t} \/ ~cb_{j,t} \/ sa_{i,j}       s_i + l_i >= t + 1 >= s_j + 1
        //
        // with the first taking `s_j >= t` from the order literal's defining
        // row where j's window opens at t, and so carrying that literal, which
        // the boundary pin makes a unit. The pin is then a `rup`.
        PolBuilder finish;
        finish.add(nobody);
        for (auto j : candidates) {
            auto guard = starts_at.at(j);
            std::map<size_t, ProofLine> pinned;
            for (auto i : candidates) {
                if (i == j)
                    continue;
                PolBuilder before;
                before.add(half_of(tracker, v.cb(i, t), ReificationHalf::Implies));
                if (had_window_before(j))
                    before.add(half_of(tracker, v.cb(j, t - 1_i), ReificationHalf::ImpliedBy));
                else
                    before.add(opening_rows.at(j));
                before.add(half_of(tracker, v.sb(i, j), ReificationHalf::ImpliedBy));
                auto before_line = before.saturate().emit(logger, ProofLevel::Top);

                PolBuilder after;
                after.add(half_of(tracker, v.ca(i, t), ReificationHalf::Implies));
                after.add(half_of(tracker, v.cb(j, t), ReificationHalf::Implies));
                after.add(half_of(tracker, v.sa(i, j), ReificationHalf::ImpliedBy));
                auto after_line = after.saturate().emit(logger, ProofLevel::Top);

                // The pin, `~starts_at_j \/ ~cact_{i,t} \/ sact_{i,j}`, as a
                // pol rather than a `rup`: the two clauses above and sact's
                // reverse half leave cb_{i,t}, ca_{i,t} and i's presence, which
                // cact's forward half cancels, and cb_{j,t} with cb_{j,t-1},
                // which starts_at_j's forward half cancels --- or, where j's
                // window opens at t, cb_{j,t} with the order literal, which the
                // boundary pin does. Degree one throughout, so saturating gives
                // the clause. Checking a pol is arithmetic, where a `rup` is a
                // propagation over a database that grows with every time point.
                PolBuilder pin;
                pin.add(before_line);
                pin.add(after_line);
                pin.add(half_of(tracker, v.sact(i, j), ReificationHalf::ImpliedBy));
                pin.add(half_of(tracker, v.cact(i, t), ReificationHalf::Implies));
                if (auto forward = starts_at_forward.find(j); forward != starts_at_forward.end())
                    pin.add(forward->second);
                else if (auto opening = opening_pins.find(j); opening != opening_pins.end())
                    pin.add(opening->second);
                pinned.emplace(i, pin.saturate().emit(logger, ProofLevel::Top));
            }

            // The diagonal, as in the scan: closed by unit propagation over j's
            // own flags.
            optional<ProofLine> diagonal_pin;
            if (auto diagonal = v.sact_diagonal(j))
                diagonal_pin = logger.emit_rup_proof_line(WPBSum{} + 1_i * ! guard + 1_i * ! v.cact(j, t) + 1_i * *diagonal >= 1_i, ProofLevel::Top);

            // Weighted by j's coefficient in `nobody`, so that starts_at_j
            // cancels exactly rather than leaving a residue saturation cannot
            // remove.
            finish.add(emit_case(v, t, candidates, j, guard, pinned, diagonal_pin, target_reverse), coefficient.at(j));
        }

        // What is left is the target at some coefficient, against degree D;
        // saturating brings the coefficient down to D, and at the base dividing
        // by it gives the unit.
        finish.saturate();
        if (! previous)
            finish.divide_by(constant_value_of(inputs.capacity) + 1_i);
        auto target_holds = finish.emit(logger, ProofLevel::Top);

        return unwrap_target(v, target, target_flag, target_forward, target_holds);
    }
}

auto gcs::innards::recover_cumulative_capacity_row(ProofLogger & logger, const CumulativeInputs & inputs, CheckpointRecoveryCache & cache, Integer t)
    -> optional<ProofLine>
{
    if (auto already = cache.recovered.find(t); already != cache.recovered.end())
        return already->second;
    if (! cumulative_checkpoint_recovery_applies(inputs, logger))
        return nullopt;

    Vocabulary v{logger, inputs, logger.names_and_ids_tracker()};
    if (v.candidates(t).empty())
        return nullopt;

    // Where a chain can start: below every window, the load is nothing, and a
    // constant capacity that is not negative bounds it.
    auto chain_base = is_constant_variable(inputs.capacity) && constant_value_of(inputs.capacity) >= 0_i;

    // How far below t to look for a row to chain up from. A chain step is
    // quadratic in the candidates and the scan cubic, so a run of up to about
    // as many steps as there are candidates is no dearer than one scan, and
    // every row it passes through is cached for whatever asks next.
    //
    // Reaching further measured faster on Pack_d (m^2: 9.4 s of checking on
    // pack030 against 14.5 s), the scan's lines being mostly `rup`s. It was
    // not taken: every extra step recovers a row nothing cited, and those rows
    // standing in the database were enough to let two other rules' mutation
    // fixtures close their corrupted derivations by unit propagation. Making
    // the scan's own steps pols is the better fix for the scan's cost.
    auto reach = Integer(static_cast<long long>(v.candidates(t).size()));
    auto from = t - 1_i;
    while (from >= t - reach && ! cache.recovered.contains(from) && ! v.candidates(from).empty())
        --from;
    auto chainable = cache.recovered.contains(from) || (v.candidates(from).empty() && chain_base);

    auto recover_one = [&](Integer u, bool by_chain) -> ProofLine {
        auto candidates = v.candidates(u);
        if (trivially_fits(v, candidates, u))
            return logger.emit_rup_proof_line(per_time_capacity_row(logger, inputs, u), ProofLevel::Top);
        if (by_chain) {
            auto previous = cache.recovered.find(u - 1_i);
            auto chained = recover_by_chain(v, u, candidates, previous == cache.recovered.end() ? nullopt : make_optional(previous->second));
            if (chained)
                return *chained;
        }
        return recover_by_scan(v, cache, u, candidates);
    };

    if (! chainable) {
        auto row = recover_one(t, false);
        cache.recovered.emplace(t, row);
        return row;
    }

    for (auto u = from + 1_i; u <= t; ++u) {
        // Every row from here up has the one below it, except at the base,
        // where there is nothing below to have.
        auto row = recover_one(u, true);
        cache.recovered.emplace(u, row);
    }
    return cache.recovered.at(t);
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

        logger.emit(ImpliesProofRule{*recovered}, per_time_capacity_row(logger, inputs, t), ProofLevel::Top);
    }
    logger.emit_proof_comment("#780 checkpoint recovery ends");
}
