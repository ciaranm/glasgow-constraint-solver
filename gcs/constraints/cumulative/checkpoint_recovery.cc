#include <gcs/constraints/cumulative/checkpoint_recovery.hh>
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

    // The label of one half of a flag's reification. These flags all come from
    // create_proof_flag_values_fully_reifying, whose halves are labelled off
    // name_of --- not off pb_file_string_for, which is what the flags with no
    // ConstraintID to key them use.
    auto half_of(const NamesAndIDsTracker & tracker, const ProofFlag & flag, const string & which) -> ProofLineLabel
    {
        return ProofLineLabel{tracker.name_of(flag) + which};
    }

    // The reification coefficient a forward half was emitted with, which is
    // what a pol has to multiply the flag by for the guard terms to cancel
    // rather than leave a residue. Asked rather than assumed, exactly as
    // Disjunctive's sorting-network certificate asks it.
    auto guard_coefficient(NamesAndIDsTracker & tracker, const WPBSumLE & ineq, const ProofFlag & flag) -> Integer
    {
        return -tracker.reification_shape(ineq, HalfReifyOnConjunctionOf{{flag}}).reif_coefficient;
    }
}

auto gcs::innards::cumulative_checkpoint_recovery_applies(const CumulativeInputs & inputs, const ProofLogger & logger) -> bool
{
    if (inputs.active_tasks.empty())
        return false;
    if (! is_constant_variable(inputs.capacity))
        return false;
    for (auto i : inputs.active_tasks) {
        if (inputs.presence[i] || ! is_constant_variable(inputs.lengths[i]) || ! is_constant_variable(inputs.heights[i]))
            return false;
        // The block has to be in the model to be recovered from. Asking for one
        // task's row is enough: the encoding writes them for every active task
        // or for none.
        if (! logger.names_and_ids_tracker().constraint_row_label(inputs.owner, Data::checkpoint_row_role(i)))
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
    auto capacity = constant_value_of(inputs.capacity);
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

    // The row being recovered, as the model states it: the load at t is within
    // the capacity. In the form the derivation ends on, which is the negated
    // one, this has degree `total - capacity`.
    WPBSum load;
    Integer total = 0_i;
    for (auto i : candidates) {
        load += height(i) * cact(i);
        total += height(i);
    }
    auto degree = total - capacity;

    // Nothing to argue about: even every candidate at once fits. The row is a
    // tautology over the flags' own bounds, so it needs no checkpoint at all.
    if (degree <= 0_i) {
        auto trivial = logger.emit_rup_proof_line(move(load) <= capacity, ProofLevel::Top);
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
            pol.add(half_of(tracker, sb(i, j), "[f]"));
            pol.add(half_of(tracker, sb(j, i), "[f]"));
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
                pol.add(half_of(tracker, sb(a, b), "[r]"));
                pol.add(half_of(tracker, sb(b, c), "[r]"));
                pol.add(half_of(tracker, sb(a, c), "[f]"));
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
            pol.add(half_of(tracker, ca(i), "[r]"));
            pol.add(half_of(tracker, cb(j), "[r]"));
            pol.add(half_of(tracker, sa(i, j), "[f]"));
            pol.saturate().emit(logger, ProofLevel::Top);
        }

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
    auto target = move(load) <= capacity;
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
            if (i != j && (t < inputs.per_task_t_lo[i] || t > inputs.per_task_t_hi[i]))
                pol.weaken(sact(i, j), tracker);
        size_t p = 0;
        for (auto i : candidates)
            if (i != j)
                pol.add(pinned[p++], height(i));
        // j's own term is the one the checkpoint row folded into its right hand
        // side, so nothing pins it and nothing cancels against it. It belongs on
        // the row all the same --- j is one of the tasks whose load is being
        // bounded --- so it goes on as a literal axiom, which adds the term
        // without moving the degree. What stands now is the target row, guarded
        // by j being the latest starter.
        pol.add(! cact(j), height(j), tracker);

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

auto gcs::innards::check_recovered_cumulative_capacity_rows(ProofLogger & logger, const CumulativeInputs & inputs) -> void
{
    if (! cumulative_checkpoint_recovery_applies(inputs, logger))
        return;

    // Bracketed, so that run_checkpoint_recovery_leak_check.bash can cut the
    // proof here and re-check the prefix against an OPB with no per-time
    // capacity rows in it. That is the only thing that says the recovery is not
    // quietly leaning, through one of its rups, on a row the encoding is about
    // to lose.
    logger.emit_proof_comment("#780 checkpoint recovery begins");
    CheckpointRecoveryCache cache;
    for (const auto & [t, model_row] : inputs.capacity_lines) {
        auto recovered = recover_cumulative_capacity_row(logger, inputs, cache, t);
        if (! recovered)
            continue;

        WPBSum load;
        for (auto i : inputs.active_tasks)
            if (t >= inputs.per_task_t_lo[i] && t <= inputs.per_task_t_hi[i])
                load += constant_value_of(inputs.heights[i]) * inputs.active_flags[i][(t - inputs.per_task_t_lo[i]).raw_value];
        logger.emit(ImpliesProofRule{*recovered}, move(load) <= constant_value_of(inputs.capacity), ProofLevel::Top);
    }
    logger.emit_proof_comment("#780 checkpoint recovery ends");
}
