#include <gcs/constraints/disjunctive/disjunctive.hh>
#include <gcs/constraints/disjunctive/hints.hh>
#include <gcs/constraints/innards/task_presence.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <algorithm>
#include <map>
#include <memory>
#include <optional>
#include <utility>
#include <variant>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_optional;
using std::make_pair;
using std::make_unique;
using std::max;
using std::min;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::size_t;
using std::unique_ptr;
using std::vector;

Disjunctive::Disjunctive(vector<IntegerVariableID> starts, vector<IntegerVariableID> lengths) : _starts(move(starts)), _lengths(move(lengths))
{
    if (_starts.size() != _lengths.size())
        throw InvalidProblemDefinitionException{"Disjunctive: starts and lengths must have the same size"};
    // Constant durations are checked here; variable durations are checked
    // against their root lower bound in prepare().
    for (const auto & l : _lengths)
        if (is_constant_variable(l) && constant_value_of(l) < 0_i)
            throw InvalidProblemDefinitionException{"Disjunctive: lengths must be non-negative"};
}

Disjunctive::Disjunctive(vector<IntegerVariableID> starts, vector<Integer> lengths) : Disjunctive(move(starts), as_constant_variables(lengths))
{
}

Disjunctive::Disjunctive(vector<IntegerVariableID> starts, vector<IntegerVariableID> lengths, vector<IntegerVariableID> presences) :
    Disjunctive(move(starts), move(lengths))
{
    _presences = move(presences);
    if (_starts.size() != _presences.size())
        throw InvalidProblemDefinitionException{"Disjunctive: starts and presences must have the same size"};
    // A constant presence is checked here, by the rule that resolves it; a
    // variable one is checked in prepare(), where its domain first becomes
    // available.
    for (const auto & p : _presences)
        (void)task_presence(make_optional(p), "Disjunctive");
}

auto Disjunctive::with_strict(std::optional<bool> strict) -> Disjunctive &
{
    _strict = strict.value_or(true);
    return *this;
}

auto Disjunctive::with_rules(DisjunctiveRules rules) -> Disjunctive &
{
    _rules = rules;
    return *this;
}

auto Disjunctive::with_proof_mutation(DisjunctiveProofMutation mutation) -> Disjunctive &
{
    _proof_mutation = mutation;
    return *this;
}

auto Disjunctive::with_presence_mutation(DisjunctivePresenceMutation mutation) -> Disjunctive &
{
    _presence_mutation = mutation;
    return *this;
}

auto Disjunctive::presences() const -> const vector<IntegerVariableID> &
{
    return _presences;
}

auto Disjunctive::clone() const -> unique_ptr<Constraint>
{
    auto cloned = _presences.empty() ? make_unique<Disjunctive>(_starts, _lengths) : make_unique<Disjunctive>(_starts, _lengths, _presences);
    cloned->with_strict(_strict);
    cloned->with_rules(_rules);
    cloned->with_proof_mutation(_proof_mutation);
    cloned->with_presence_mutation(_presence_mutation);
    return cloned;
}

auto Disjunctive::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    auto n = _starts.size();

    // Resolve length snapshots. _length_vals is the constant value (0
    // placeholder for a variable, where _lengths[i] is read from the state).
    _length_vals.assign(n, 0_i);
    for (size_t i = 0; i < n; ++i) {
        if (is_constant_variable(_lengths[i]))
            _length_vals[i] = constant_value_of(_lengths[i]);
        else if (initial_state.lower_bound(_lengths[i]) < 0_i)
            throw InvalidProblemDefinitionException{"Disjunctive: lengths must be non-negative"};
    }

    // Resolve each task's presence to the variable its separation clauses have
    // to carry a disjunct on, or nullopt when the task is unconditionally
    // present, by the rule Cumulative resolves its presences with --- the two
    // constraints are alternative encodings of overlapping problems, so a
    // presence argument one honours and the other drops would be a difference
    // in meaning between them.
    _presence.assign(n, nullopt);
    vector<bool> never_present(n, false);
    for (size_t i = 0; i < n; ++i) {
        auto resolved = task_presence(_presences.empty() ? nullopt : make_optional(_presences[i]), "Disjunctive");
        _presence[i] = resolved.literal;
        never_present[i] = resolved.never_present;

        // Only now are the domains available, which is why a variable presence
        // is range-checked here rather than in the constructor.
        if (resolved.literal && ! is_constant_variable(*resolved.literal)) {
            auto [lo, hi] = initial_state.bounds(*resolved.literal);
            if (lo < 0_i || hi > 1_i)
                throw InvalidProblemDefinitionException{"Disjunctive: presences must be within {0, 1}"};
        }
    }

    // In non-strict mode, a task that is definitely zero-length cannot constrain
    // any other task, so drop it. A constant zero is dropped here; a variable
    // duration that *can* be zero stays active and gets a zero-length escape
    // flag (it might still take a positive value during search). In strict mode
    // every task participates (a zero-length task may not sit strictly inside
    // another's active interval). A constantly-absent task is dropped in either
    // mode: it occupies no time, so it constrains nothing and nothing
    // constrains it, and it must appear nowhere in the encoding at all.
    _active_tasks.reserve(n);
    for (size_t i = 0; i < n; ++i) {
        if (never_present[i])
            continue;
        if (! _strict && is_constant_variable(_lengths[i]) && _length_vals[i] == 0_i)
            continue;
        _active_tasks.push_back(i);
    }

    if (_active_tasks.size() < 2)
        return false;

    // Non-strict mode: every variable-duration task gets a zero-length escape
    // in the separation clause, matching cake_pb_cp, which adds the zw
    // disjunct for every variable-length argument regardless of its bounds.
    // Gating it on lower_bound == 0 changes the labelled @c[id][.._sepal1]
    // row's content, and proofs that pol-cite that label then fail to
    // chain-verify (issue #482). An always-positive duration's escape is just
    // statically false; add_escape_pins refutes it in one RUP step. The
    // propagator already ignores zero-mandatory tasks via lb(l).
    _zero_escape.assign(n, 0);
    if (! _strict)
        for (auto i : _active_tasks)
            _zero_escape[i] = is_constant_variable(_lengths[i]) ? 0 : 1;

    return true;
}

auto Disjunctive::define_proof_model(ProofModel & model, const State &) -> void
{
    // Declarative pairwise OPB encoding:
    //   for each unordered pair (i, j) of participating tasks:
    //     before_{i,j} <-> starts[i] + lengths[i] <= starts[j]
    //     before_{j,i} <-> starts[j] + lengths[j] <= starts[i]
    //   then one clause per pair:
    //     before_{i,j} v before_{j,i} [ v presences[i] = 0 v presences[j] = 0 ]
    //
    // This is the only thing that goes into the OPB: the constraint's
    // declarative meaning, free of time-table or other propagator-specific
    // scaffolding. It is also all the proof scaffolding there is: every
    // justification is a pol over these rows and order-literal definition
    // rows, so the line numbers of both reification halves of each before
    // flag, and of each pairwise clause, are stored for the propagator.
    // For a task with a variable duration the duration term stays on the
    // flag's left-hand side and cancels against the duration's bound row in
    // the same pol, so no proof-only end = s + l variable is needed.

    // Non-strict mode: a "duration <= 0" escape flag per variable-duration
    // task, added as a disjunct to the separation clause below (a zero-length
    // task does not constrain). nullopt otherwise.
    _zero.assign(_starts.size(), nullopt);
    for (auto i : _active_tasks)
        if (_zero_escape[i])
            // cake_pb_cp names the zero-duration escape x[id][i][zw].
            _zero[i] = model.create_proof_flag_fully_reifying(
                _constraint_id, vector<long long>{static_cast<long long>(i)}, "zw", WPBSum{} + 1_i * _lengths[i] <= 0_i);

    // before_{i,j} <-> s_i + l_i <= s_j. For a constant duration this folds to
    // s_i - s_j <= -l (byte-identical to the constant-only implementation); for
    // a variable duration the length term stays on the left.
    auto emit_before = [&](size_t i, size_t j) -> BeforeFlagData {
        // cake_pb_cp names the "task i finishes before task j starts" flag
        // x[id][i_j][bf]; match it for verified-encoding compatibility.
        auto flag = model.create_proof_flag(_constraint_id, vector<long long>{static_cast<long long>(i), static_cast<long long>(j)}, "bf");
        auto ineq = is_constant_variable(_lengths[i]) ? (WPBSum{} + 1_i * _starts[i] + -1_i * _starts[j] <= -_length_vals[i])
                                                      : (WPBSum{} + 1_i * _starts[i] + 1_i * _lengths[i] + -1_i * _starts[j] <= 0_i);
        auto [fwd, rev] = model.add_two_way_reified_constraint(ineq, flag);
        return BeforeFlagData{flag, fwd, rev};
    };
    for (size_t a = 0; a < _active_tasks.size(); ++a) {
        auto i = _active_tasks[a];
        for (size_t b = a + 1; b < _active_tasks.size(); ++b) {
            auto j = _active_tasks[b];
            auto data_ij = emit_before(i, j);
            auto data_ji = emit_before(j, i);
            // A zero-length task escapes the separation clause (non-strict).
            auto clause_sum = WPBSum{} + 1_i * data_ij.flag + 1_i * data_ji.flag;
            for (auto r : {i, j})
                if (_zero[r])
                    clause_sum += 1_i * *_zero[r];
            // And so does an absent one, which is the whole of what optional
            // tasks add to this encoding: the presence literal is the {0, 1}
            // variable's single PB atom, so a pair of optional tasks costs two
            // more terms in one clause they already had --- no extra flag, no
            // extra row, and nothing else in the encoding has to know whether a
            // task is optional. In particular the before flags stay reified
            // *unconditionally* on the arithmetic, which is what keeps every
            // justification below a pol over the same rows as before.
            for (auto r : {i, j})
                if (_presence[r])
                    clause_sum += 1_i * (*_presence[r] == 0_i);
            // cake_pb_cp labels the separation clause @c[id][<i>_<j>sepal1].
            auto clause =
                model.add_labelled_constraint(_constraint_id, std::to_string(i) + "_" + std::to_string(j) + "sepal1", move(clause_sum) >= 1_i);
            _before_flags.emplace(std::make_pair(i, j), data_ij);
            _before_flags.emplace(std::make_pair(j, i), data_ji);
            _clause_lines.emplace(std::make_pair(i, j), clause);
        }
    }
}

auto Disjunctive::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    for (auto i : _active_tasks) {
        triggers.on_bounds.emplace_back(_starts[i]);
        // A rise in a task's minimum duration extends its mandatory part, so
        // re-fire on variable-duration bound changes too.
        if (! is_constant_variable(_lengths[i]))
            triggers.on_bounds.emplace_back(_lengths[i]);
        // A task starts blocking others the moment its presence is fixed to 1,
        // and stops being anything at all when it is fixed to 0, so an optional
        // task's presence has to wake the propagator as much as its start does.
        if (_presence[i] && ! is_constant_variable(*_presence[i]))
            triggers.on_instantiated.emplace_back(*_presence[i]);
    }

    propagators.install(
        constraint_id(),
        [starts = move(_starts), lengths = move(_length_vals), length_vars = move(_lengths), zero = move(_zero), strict = _strict,
            active_tasks = move(_active_tasks), before_flags = move(_before_flags), clause_lines = move(_clause_lines), presence = move(_presence),
            rules = _rules, mutation = _proof_mutation, presence_mutation = _presence_mutation,
            owner = constraint_id()](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // Current guaranteed (min) and possible (max) duration of task i:
            // for a constant duration both are the value; for a variable
            // duration they are the live lower / upper bounds.
            auto is_var_len = [&](size_t i) -> bool { return ! is_constant_variable(length_vars[i]); };
            auto min_len = [&](size_t i) -> Integer { return is_var_len(i) ? state.lower_bound(length_vars[i]) : lengths[i]; };
            auto max_len = [&](size_t i) -> Integer { return is_var_len(i) ? state.upper_bound(length_vars[i]) : lengths[i]; };

            // A task with no presence variable is always here. An optional one
            // is here only once its presence is fixed to 1: until then it
            // occupies no time as far as this propagator is concerned, blocks
            // nothing, and nothing may be inferred about its start, since a
            // prune that is only valid when the task is present would be plain
            // wrong if it turns out absent. Fixed to 0, it is gone for good and
            // every loop below skips it.
            auto is_present = [&](size_t i) -> bool { return ! presence[i] || state.lower_bound(*presence[i]) == 1_i; };
            auto is_absent = [&](size_t i) -> bool { return presence[i] && state.upper_bound(*presence[i]) == 0_i; };

            // Presence enters a reason as an explicit literal per task known
            // present, rather than by putting the variable in the reason's
            // variable list: an undecided presence has no fact to record (a task
            // not known present simply constrains nothing, and staying that way
            // is monotone as the domain shrinks), and generic_reason would
            // contribute the pair of trivial bounds 0 <= p <= 1 for it, which
            // says nothing and costs an order atom on a variable whose whole
            // encoding is one PB literal. Every inference below reasons only
            // about tasks known present, so this one list serves all of them.
            // The snapshot is taken once per call and stays accurate: the only
            // presence this propagator ever changes is one it fixes to 0, and
            // those were undecided, so absent from the list to begin with.
            ReasonLiterals presence_lits;
            for (auto i : active_tasks)
                if (presence[i] && is_present(i))
                    presence_lits.push_back(*presence[i] == 1_i);
            auto reason_over = [&](const vector<IntegerVariableID> & vars) -> Reason { return with_extra(generic_reason(vars), presence_lits); };

            // The pairwise proof vocabulary. Everything the propagator infers
            // is justified through the encoded before-flags: a pol over a
            // flag's [r] row (flag -> s_a + l_a <= s_b) plus one bound-literal
            // definition row per operand cancels the integer terms exactly,
            // leaving a clause over the flag's negation and the residual
            // order literals, which the closing reason-wrapped RUPs then
            // unit-propagate. The pol is load-bearing: bare RUP cannot
            // transfer a bound row's cap into the reification row's slack
            // when the overlap margin is smaller than the residual
            // bit-encoding range. See dev_docs/disjunctive-proof-logging.md.
            //
            // cond_a / cond_b are the bound literals cited for s_a and s_b
            // (nullopt for a constant start, whose value is already folded
            // into the flag's row); a variable duration l_a additionally
            // cites its current lower bound (the reason covers it).
            auto emit_before_pol = [&](size_t a, size_t b, const optional<IntegerVariableCondition> & cond_a,
                                       const optional<IntegerVariableCondition> & cond_b) -> void {
                auto & tracker = logger->names_and_ids_tracker();
                PolBuilder pol;
                pol.add(before_flags.at(make_pair(a, b)).forward_line);
                // Add cond's order-literal definition row, which swaps the
                // operand's bit terms for a single residual literal. When the
                // literal maps directly onto one encoding bit (a one-bit
                // domain, or a top-bit threshold) there is no definition row
                // and nothing to add: the operand's term already normalises
                // to that residual, and the threshold's bit alignment bounds
                // the remaining low-bit residual by the bound's slack.
                // (Adding the literal axiom via add_for_literal would instead
                // cancel the term outright and lose the bound.)
                auto add_defining_row = [&](const IntegerVariableCondition & cond) -> void {
                    auto item = tracker.need_pol_item_defining_literal(cond);
                    if (auto * line = std::get_if<ProofLine>(&item))
                        pol.add(*line);
                };
                if (cond_a)
                    add_defining_row(*cond_a);
                if (is_var_len(a))
                    add_defining_row(length_vars[a] >= state.lower_bound(length_vars[a]));
                if (cond_b)
                    add_defining_row(*cond_b);
                pol.saturate().emit(*logger, ProofLevel::Temporary);
            };

            // The current-bound literals on a task's start, or nullopt for a
            // constant start (a constant has no defining literal to cite).
            auto start_lb_lit = [&](size_t i) -> optional<IntegerVariableCondition> {
                if (is_constant_variable(starts[i]))
                    return nullopt;
                return starts[i] >= state.lower_bound(starts[i]);
            };
            auto start_ub_lit = [&](size_t i) -> optional<IntegerVariableCondition> {
                if (is_constant_variable(starts[i]))
                    return nullopt;
                return starts[i] < state.upper_bound(starts[i]) + 1_i;
            };

            // Non-strict mode: every task involved in an inference has a
            // positive guaranteed duration (it contributes a mandatory part
            // or footprint), so its zero-length escape flag is false. Pin
            // those flags false (RUP under reason, from the duration's lower
            // bound) so the separation clauses reduce to their before-flag
            // disjunctions. No-op in strict mode / for always-positive
            // durations.
            auto pin_escapes = [&](const ReasonLiterals & reason, const vector<size_t> & tasks) -> void {
                for (auto r : tasks)
                    if (zero[r])
                        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * *zero[r] <= 0_i, ProofLevel::Temporary);
            };

            // Time-table consistency, specialised to heights = 1 and
            // capacity = 1. Mandatory part of task i is [lst_i, eet_i)
            // where lst_i = ub(s_i) and eet_i = lb(s_i) + l_i: the slice it
            // must occupy regardless of where it starts. Two tasks whose
            // mandatory parts overlap is infeasible, and any per-task start
            // that would force a mandatory-part collision is excluded.
            //
            // Zero-length tasks contribute nothing to the profile but in
            // strict mode are still constrained: a zero-length task's
            // point may not sit strictly inside any other task's open
            // active interval. The TT pass misses that case; we catch it
            // below with an all-fixed pairwise check.
            //
            // An absent task is out of the horizon as well as out of the
            // profile: its start is unconstrained, so leaving it in would size
            // mand_load by a domain nothing below ever indexes. An *undecided*
            // task stays in, contributing no load but keeping room for the
            // placements the falsification below has to scan.
            bool any = false;
            Integer t_lo = 0_i, t_hi = -1_i;
            for (auto i : active_tasks) {
                if (max_len(i) == 0_i || is_absent(i))
                    continue;
                auto [s_lo, s_hi] = state.bounds(starts[i]);
                auto lo = s_lo, hi = s_hi + max_len(i) - 1_i;
                if (! any || lo < t_lo)
                    t_lo = lo;
                if (! any || hi > t_hi)
                    t_hi = hi;
                any = true;
            }

            if (any) {
                // Variable durations join the reason for the push proofs (the
                // pols and mandatory parts read lb(l)). For a constant-only
                // instance this is just the starts, leaving the proof
                // byte-identical.
                auto push_reason_vars = starts;
                for (auto i : active_tasks)
                    if (is_var_len(i))
                        push_reason_vars.push_back(length_vars[i]);

                // The mutation switches, unpacked once for both dichotomies
                // below. Everything but a mutation lane passes None, so all
                // four come out false; see innards/disjunctive_mutations.hh
                // for what each one breaks and why VeriPB has to notice.
                struct DichotomyMutation
                {
                    bool emit_nothing, skip_refutation, skip_target_fold, loose_bound;
                };
                auto unpack_mutation = [](const DisjunctiveProofMutation & mut) -> DichotomyMutation {
                    return {std::holds_alternative<disjunctive_proof_mutation::EmitNothing>(mut),
                        std::holds_alternative<disjunctive_proof_mutation::SkipRefutation>(mut),
                        std::holds_alternative<disjunctive_proof_mutation::SkipTargetFold>(mut),
                        std::holds_alternative<disjunctive_proof_mutation::LooseDetectionBound>(mut)};
                };

                // The two pols of one pairwise dichotomy on task j's lower
                // bound, against a single other task k: with the running bound
                // established, j's next lb(l_j) slots reach past ub(s_k), so
                // "j finishes before k starts" is impossible and the encoded
                // pairwise clause forces "k finishes before j starts", which
                // advances j's bound to `target` in one dichotomy. Both
                // time-tabling's push chains and detectable precedences infer
                // through this same shape; only how they choose k and target
                // differs. `mut` is honest for everything but a mutation lane.
                auto emit_lb_dichotomy = [&](size_t j, size_t k, Integer bound, Integer target, const DisjunctiveProofMutation & mut) -> void {
                    auto [emit_nothing, skip_refutation, skip_target_fold, loose_bound] = unpack_mutation(mut);
                    if (emit_nothing)
                        return;
                    // Left branch: j finishing before k contradicts the
                    // running bound -- s_j >= bound plus lb(l_j) reaches past
                    // ub(s_k), forcing bf_{j,k} false.
                    if (! skip_refutation)
                        emit_before_pol(j, k, starts[j] >= (loose_bound ? bound - 1_i : bound), start_ub_lit(k));
                    // Right branch: k finishing before j puts s_j at k's
                    // earliest end or later, folded onto the target order
                    // literal's definition row: bf_{k,j} -> s_j >= target.
                    if (! skip_target_fold)
                        emit_before_pol(k, j, start_lb_lit(k), starts[j] < target);
                };
                // The mirror image, on j's upper bound: k finishing before j
                // is impossible under the running bound -- s_j would be at k's
                // earliest end or later, past bound -- so j finishes before k,
                // capping s_j at k's latest start minus lb(l_j).
                auto emit_ub_dichotomy = [&](size_t j, size_t k, Integer bound, Integer target, const DisjunctiveProofMutation & mut) -> void {
                    auto [emit_nothing, skip_refutation, skip_target_fold, loose_bound] = unpack_mutation(mut);
                    if (emit_nothing)
                        return;
                    if (! skip_refutation)
                        emit_before_pol(k, j, start_lb_lit(k), starts[j] < bound + (loose_bound ? 2_i : 1_i));
                    if (! skip_target_fold)
                        emit_before_pol(j, k, starts[j] >= target + 1_i, start_ub_lit(k));
                };

                // One step of a time-tabling push chain, which is one
                // dichotomy plus, for a non-final step, a deposit of the
                // advanced bound under the reason so the next step's left
                // branch unit-propagates from it. The final target is exactly
                // the inferred bound, which the framework's closing RUP
                // concludes. `bound` is the running bound the step starts from
                // (established by the reason for the first step, by the
                // previous step's deposit after).
                //
                // `absent` is the "or task j is not here at all" disjunct that
                // the presence falsification below carries on every deposit, so
                // each step reads "either j starts later than this, or j is not
                // here"; nullopt for an ordinary push, whose task is known
                // present. The dichotomy's two pols are the same either way:
                // they are arithmetic over the before flags, which stay reified
                // unconditionally, so presence never reaches them.
                auto emit_lb_chain_step = [&](size_t j, size_t k, Integer bound, Integer target, bool final,
                                              const optional<IntegerVariableCondition> & absent, const ReasonLiterals & reason) -> void {
                    emit_lb_dichotomy(j, k, bound, target, disjunctive_proof_mutation::None{});
                    if (! final) {
                        auto deposit = WPBSum{} + 1_i * (starts[j] >= target);
                        if (absent)
                            deposit += 1_i * *absent;
                        logger->emit_rup_proof_line_under_reason(reason, move(deposit) >= 1_i, ProofLevel::Temporary);
                    }
                };
                auto emit_ub_chain_step = [&](size_t j, size_t k, Integer bound, Integer target, bool final, const ReasonLiterals & reason) -> void {
                    emit_ub_dichotomy(j, k, bound, target, disjunctive_proof_mutation::None{});
                    if (! final)
                        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (starts[j] < target + 1_i) >= 1_i, ProofLevel::Temporary);
                };

                auto range = (t_hi - t_lo + 1_i).raw_value;
                vector<int> mand_load(range, 0);

                // Only a task known present puts a mandatory part into the
                // profile. An undecided one might not be here at all, so its
                // mandatory part is not mandatory.
                for (auto i : active_tasks) {
                    if (min_len(i) == 0_i || ! is_present(i))
                        continue;
                    auto lst = state.upper_bound(starts[i]);
                    auto eet = state.lower_bound(starts[i]) + min_len(i);
                    if (lst < eet)
                        for (Integer t = lst; t < eet; ++t)
                            ++mand_load[(t - t_lo).raw_value];
                }

                // The mandatory-overlap contradiction runs whatever the rule
                // selection is: at an all-fixed leaf every task's mandatory part
                // is its whole active interval, so this scan is what makes the
                // propagator a *checker*, and a rule selection that stopped it
                // running would not be a weakening of propagation but a solver
                // that reports assignments violating the constraint. Only the
                // bound pushes below are time-tabling's to switch off.
                for (auto idx = 0; idx < range; ++idx)
                    if (mand_load[idx] > 1) {
                        auto violating_t = t_lo + Integer{idx};
                        // Find the first two tasks whose mandatory parts cover
                        // violating_t. With h=1, c=1, two is enough: their
                        // pairwise separation clause is already violated.
                        size_t pi = 0, pj = 0;
                        bool got_first = false, got_second = false;
                        for (auto i : active_tasks) {
                            if (min_len(i) == 0_i || ! is_present(i))
                                continue;
                            auto lst = state.upper_bound(starts[i]);
                            auto eet = state.lower_bound(starts[i]) + min_len(i);
                            if (lst < eet && violating_t >= lst && violating_t < eet) {
                                if (! got_first) {
                                    pi = i;
                                    got_first = true;
                                }
                                else {
                                    pj = i;
                                    got_second = true;
                                    break;
                                }
                            }
                        }
                        if (! got_second)
                            throw UnexpectedException{"Disjunctive: mand_load > 1 without two contributing tasks"};

                        auto justify = [&, pi, pj](const ReasonLiterals & reason) -> void {
                            pin_escapes(reason, {pi, pj});
                            // The mandatory parts overlap at violating_t, so
                            // neither task can finish before the other starts:
                            // each before flag's [r] row plus the mandatory
                            // bounds (lb of the finisher's start and duration,
                            // ub of the other's start) is infeasible, so one
                            // pol per flag forces it false under the reason,
                            // and the separation clause unit-fails in the
                            // framework's closing reason-wrapped RUP.
                            emit_before_pol(pi, pj, start_lb_lit(pi), start_ub_lit(pj));
                            emit_before_pol(pj, pi, start_lb_lit(pj), start_ub_lit(pi));
                        };

                        // The pols cite lb(l) for variable-length tasks, so
                        // those durations must be part of the reason.
                        auto reason_vars = starts;
                        if (is_var_len(pi))
                            reason_vars.push_back(length_vars[pi]);
                        if (is_var_len(pj))
                            reason_vars.push_back(length_vars[pj]);
                        inference.contradiction(
                            logger, JustifyExplicitly{justify, ThenRUP::Yes, hints::Disjunctive{owner}}, reason_over(reason_vars));
                        return PropagatorState::DisableUntilBacktrack;
                    }

                if (rules.time_table) {
                    // One step of an lb/ub-push chain: a single blocking task and
                    // the start bound the pair dichotomy advances to (the
                    // blocker's mandatory end for an lb-push, its latest start
                    // minus lb(l_j) for a ub-push). One step per BLOCKER, however
                    // long the blocker -- see emit_lb_dichotomy above.
                    struct ChainStep
                    {
                        size_t blocker;
                        Integer target;
                    };

                    for (auto j : active_tasks) {
                        // A task with no guaranteed duration blocks nothing and
                        // fits everywhere, so there is neither a push nor a
                        // falsification to be had from it. An absent one is not
                        // here at all.
                        if (min_len(j) == 0_i || is_absent(j))
                            continue;
                        auto [cur_lb, cur_ub] = state.bounds(starts[j]);
                        // A fixed start leaves nothing to push, but an undecided
                        // task with a fixed start can still be shown to have
                        // nowhere to go.
                        if (cur_lb == cur_ub && is_present(j))
                            continue;

                        auto lst_j = cur_ub, eet_j = cur_lb + min_len(j);
                        // Only a task known present put anything into the
                        // profile, so only that one has something to discount
                        // before asking where it could go. An undecided task's
                        // own mandatory part is not in mand_load and must not be
                        // subtracted out of it.
                        auto fits_at = [&, j](Integer s) -> bool {
                            for (Integer t = s; t < s + min_len(j); ++t) {
                                auto load = mand_load[(t - t_lo).raw_value];
                                if (is_present(j) && lst_j < eet_j && t >= lst_j && t < eet_j)
                                    --load;
                                if (load >= 1)
                                    return false;
                            }
                            return true;
                        };

                        // A blocker for a chain step at running bound `bound`: a
                        // task (other than j) whose mandatory part intersects the
                        // window [bound, bound + lb(l_j)). Every non-fitting start
                        // is blocked, so while the chain has ground to cover one
                        // exists; `better` picks the most useful of two candidate
                        // mandatory parts (deepest end for an lb-push, leftmost
                        // start for a ub-push). Reads current bounds, which may be
                        // tighter than the profile (mandatory parts only grow
                        // within a pass), hence the clipping in the chain loops
                        // below.
                        //
                        // nullopt when there is none, which a push chain treats
                        // as an internal inconsistency (must_find_blocker) but
                        // the presence falsification does not: the
                        // ClaimOneTooFar mutation deliberately runs a chain over
                        // ground that is not all blocked, and running out of
                        // blockers is exactly how it fails to close.
                        auto find_blocker = [&](size_t j, Integer bound, const auto & better) -> optional<pair<size_t, pair<Integer, Integer>>> {
                            optional<size_t> blocker;
                            pair<Integer, Integer> best_mand{0_i, 0_i};
                            for (auto k : active_tasks) {
                                // Only a task known present is in the profile,
                                // and only a task in the profile can be what
                                // made a start not fit.
                                if (k == j || min_len(k) == 0_i || ! is_present(k))
                                    continue;
                                auto lst_k = state.upper_bound(starts[k]);
                                auto eet_k = state.lower_bound(starts[k]) + min_len(k);
                                if (lst_k < eet_k && lst_k < bound + min_len(j) && eet_k > bound &&
                                    (! blocker || better(pair{lst_k, eet_k}, best_mand))) {
                                    blocker = k;
                                    best_mand = pair{lst_k, eet_k};
                                }
                            }
                            if (! blocker)
                                return nullopt;
                            return pair{*blocker, best_mand};
                        };
                        auto must_find_blocker = [&](size_t j, Integer bound, const auto & better) -> pair<size_t, pair<Integer, Integer>> {
                            auto found = find_blocker(j, bound, better);
                            if (! found)
                                throw UnexpectedException{"Disjunctive: no blocker for a push chain step"};
                            return *found;
                        };

                        // lb-push: scan upward to find the smallest fitting start,
                        // then justify with one dichotomy step per blocker, each
                        // advancing the running bound to the blocker's mandatory
                        // end -- clipped to new_lb, both because the profile may
                        // be staler than the bounds the steps cite and so the
                        // final step lands exactly on the inferred bound.
                        auto deepest_end = [](const auto & a, const auto & b) { return a.second > b.second; };
                        auto new_lb = cur_lb;
                        while (new_lb <= cur_ub && ! fits_at(new_lb))
                            ++new_lb;

                        if (! is_present(j)) {
                            // Presence falsification. The task is undecided and,
                            // if it were present, has nowhere left to start:
                            // new_lb ran off the end of its domain. Replay the
                            // lb-push chain over the whole domain with "task j is
                            // absent" carried as an extra disjunct on every
                            // deposit, so each step says "either j starts later
                            // than this, or j is not here at all". The last step
                            // deposits nothing, exactly as the last step of a
                            // push does: its target is one past j's upper bound,
                            // which the reason already refutes, so the
                            // framework's closing RUP concludes the presence.
                            //
                            // The ClaimOneTooFar mutation fires where exactly
                            // one placement is still open, so the conclusion is
                            // wrong rather than the route to it. The chain then
                            // stops short --- its last window has no blocker ---
                            // and the closing RUP has nothing to close on, which
                            // is what VeriPB must catch.
                            if (new_lb <= cur_ub &&
                                ! (std::holds_alternative<disjunctive_presence_mutation::ClaimOneTooFar>(presence_mutation) && new_lb == cur_ub))
                                continue;

                            vector<ChainStep> chain;
                            if (logger) {
                                Integer bound = cur_lb;
                                while (bound <= cur_ub) {
                                    auto found = find_blocker(j, bound, deepest_end);
                                    if (! found)
                                        break;
                                    chain.push_back(ChainStep{found->first, min(found->second.second, cur_ub + 1_i)});
                                    bound = chain.back().target;
                                }
                            }
                            if (logger && chain.empty())
                                throw UnexpectedException{"Disjunctive: no blocker for a presence falsification"};

                            auto justify = [&, j, cur_lb, chain](const ReasonLiterals & reason) -> void {
                                // The marker a test counts to show the rule
                                // fired, and counts to zero on the twin instance
                                // where it must not.
                                logger->emit_proof_comment(
                                    "disjunctive optional: task " + std::to_string(j) + " cannot be placed anywhere, so it is absent");

                                vector<size_t> involved{j};
                                for (const auto & step : chain)
                                    involved.push_back(step.blocker);
                                pin_escapes(reason, involved);

                                // Which task's absence the deposits argue about:
                                // the one being falsified, unless the WrongTask
                                // mutation points them at some other optional
                                // task.
                                auto about = j;
                                if (std::holds_alternative<disjunctive_presence_mutation::WrongTask>(presence_mutation))
                                    for (auto k : active_tasks)
                                        if (k != j && presence[k]) {
                                            about = k;
                                            break;
                                        }

                                auto steps =
                                    std::holds_alternative<disjunctive_presence_mutation::EmitNothing>(presence_mutation) ? size_t{0} : chain.size();
                                Integer bound = cur_lb;
                                for (size_t step = 0; step < steps; ++step) {
                                    emit_lb_chain_step(j, chain[step].blocker, bound, chain[step].target, step + 1 == steps,
                                        make_optional(*presence[about] == 0_i), reason);
                                    bound = chain[step].target;
                                }
                            };

                            inference.infer_equal(logger, *presence[j], 0_i, JustifyExplicitly{justify, ThenRUP::Yes, hints::Disjunctive{owner}},
                                reason_over(push_reason_vars));
                            continue;
                        }

                        if (new_lb > cur_lb) {
                            vector<ChainStep> chain;
                            if (logger) {
                                Integer bound = cur_lb;
                                while (bound < new_lb) {
                                    auto [k, mand] = must_find_blocker(j, bound, deepest_end);
                                    chain.push_back(ChainStep{k, min(mand.second, new_lb)});
                                    bound = chain.back().target;
                                }
                            }

                            auto justify = [&, j, cur_lb, chain](const ReasonLiterals & reason) -> void {
                                vector<size_t> involved{j};
                                for (const auto & step : chain)
                                    involved.push_back(step.blocker);
                                pin_escapes(reason, involved);
                                Integer bound = cur_lb;
                                for (size_t step = 0; step < chain.size(); ++step) {
                                    emit_lb_chain_step(j, chain[step].blocker, bound, chain[step].target, step + 1 == chain.size(), nullopt, reason);
                                    bound = chain[step].target;
                                }
                            };

                            inference.infer_greater_than_or_equal(logger, starts[j], new_lb,
                                JustifyExplicitly{justify, ThenRUP::Yes, hints::Disjunctive{owner}}, reason_over(push_reason_vars));
                        }

                        // ub-push: mirror of lb-push, scanning downward, each step
                        // dropping the running bound to the blocker's latest start
                        // minus lb(l_j) (the last start from which j finishes by
                        // the time the blocker must have started), clipped to
                        // new_ub.
                        auto new_ub = cur_ub;
                        while (new_ub >= cur_lb && ! fits_at(new_ub))
                            --new_ub;
                        if (new_ub < cur_ub) {
                            vector<ChainStep> chain;
                            if (logger) {
                                Integer bound = cur_ub;
                                while (bound > new_ub) {
                                    auto [k, mand] = must_find_blocker(j, bound, [](const auto & a, const auto & b) { return a.first < b.first; });
                                    chain.push_back(ChainStep{k, max(mand.first - min_len(j), new_ub)});
                                    bound = chain.back().target;
                                }
                            }

                            auto justify = [&, j, cur_ub, chain](const ReasonLiterals & reason) -> void {
                                vector<size_t> involved{j};
                                for (const auto & step : chain)
                                    involved.push_back(step.blocker);
                                pin_escapes(reason, involved);
                                Integer bound = cur_ub;
                                for (size_t step = 0; step < chain.size(); ++step) {
                                    emit_ub_chain_step(j, chain[step].blocker, bound, chain[step].target, step + 1 == chain.size(), reason);
                                    bound = chain[step].target;
                                }
                            };

                            inference.infer_less_than(logger, starts[j], new_ub + 1_i,
                                JustifyExplicitly{justify, ThenRUP::Yes, hints::Disjunctive{owner}}, reason_over(push_reason_vars));
                        }
                    }
                }

                // Detectable precedences. The precedence k << j is
                // *detectable* when j cannot finish before k starts on bounds
                // alone:
                //
                //     lb(s_j) + lb(l_j)  >  ub(s_k)
                //
                // Then before_{j,k} is false, so the separation clause forces
                // before_{k,j}: s_k + l_k <= s_j. That bounds j from below by
                // k's earliest end, and (reading the same precedence the other
                // way round) bounds k from above by j's latest start less
                // l_k:
                //
                //     s_j >= lb(s_k) + lb(l_k)      pushing the successor up
                //     s_k <= ub(s_j) - lb(l_k)      pushing the predecessor down
                //
                // Unlike time-tabling, this asks for no mandatory part on
                // either task, and that is exactly where the extra strength
                // is: when k does have one, detection says j's next lb(l_j)
                // slots reach past ub(s_k) = k's mandatory start, so the
                // window [lb(s_j), lb(s_j) + lb(l_j)) meets k's mandatory part
                // and time-tabling has already pushed j at least this far. A
                // predecessor whose mandatory part is empty pushes here and
                // nowhere else.
                //
                // Each detected precedence justifies its own push on its own,
                // so a push needs only the *best* detected predecessor (the
                // one ending latest) or successor (the one starting earliest):
                // no set-based reasoning, and no chain. Vilim's O(n log n)
                // form keeps the detected predecessors in a Theta-tree and
                // pushes to the whole set's earliest completion time, which is
                // stronger and needs an energy argument; this is the pairwise
                // version.
                //
                // The proof is one dichotomy of the shape time-tabling's push
                // chains are built from, with the blocker's mandatory part
                // playing no part -- the pol arithmetic never referred to it,
                // only the profile scan that picked the blocker did.
                //
                // Both tasks have to be known present: a precedence is a
                // statement that one of them finishes before the other starts,
                // which says nothing at all if either might not be here. That
                // rules out a *conditional* precedence, which would need the
                // presence literals inside the pols rather than only in the
                // reason; the falsification above is the only place presence
                // reaches a proof line here.
                if (rules.detectable_precedences)
                    for (auto j : active_tasks) {
                        if (min_len(j) == 0_i || ! is_present(j))
                            continue;
                        // A task whose start is already fixed has no bound to
                        // push, and nothing is lost by leaving it alone: a
                        // precedence detected between a fixed task and an
                        // unfixed one is the same precedence read the other way
                        // round, which pushes the unfixed one and fails there
                        // if it must; and two fixed tasks that collide both
                        // have mandatory parts, which is the always-on overlap
                        // contradiction above.
                        auto [cur_lb, cur_ub] = state.bounds(starts[j]);
                        if (cur_lb == cur_ub)
                            continue;

                        // One scan for both pushes: k is a detected
                        // predecessor of j when j cannot finish before k
                        // starts, and a detected successor when k cannot
                        // finish before j starts. A task with no guaranteed
                        // duration is skipped, as everywhere else here: it
                        // has no zero-length escape to pin false.
                        optional<size_t> predecessor, successor;
                        Integer predecessor_eet = 0_i, successor_lst = 0_i;
                        for (auto k : active_tasks) {
                            if (k == j || min_len(k) == 0_i || ! is_present(k))
                                continue;
                            auto [k_lb, k_ub] = state.bounds(starts[k]);
                            auto eet_k = k_lb + min_len(k);
                            if (cur_lb + min_len(j) > k_ub && (! predecessor || eet_k > predecessor_eet)) {
                                predecessor = k;
                                predecessor_eet = eet_k;
                            }
                            if (eet_k > cur_ub && (! successor || k_ub < successor_lst)) {
                                successor = k;
                                successor_lst = k_ub;
                            }
                        }

                        auto one_too_far = std::holds_alternative<disjunctive_proof_mutation::PushOneTooFar>(mutation);

                        // lb-push, to the predecessor's earliest end, clipped
                        // to one past j's upper bound: a push that wipes the
                        // domain is a contradiction, and the target has to
                        // stay somewhere the order literal exists.
                        if (predecessor) {
                            auto target = min(predecessor_eet, cur_ub + 1_i) + (one_too_far ? 1_i : 0_i);
                            if (target > cur_lb) {
                                auto justify = [&, j, k = *predecessor, cur_lb, target](const ReasonLiterals & reason) -> void {
                                    logger->emit_proof_comment(
                                        "disjunctive detectable precedence " + std::to_string(k) + "<<" + std::to_string(j) + " push=lb");
                                    pin_escapes(reason, {j, k});
                                    emit_lb_dichotomy(j, k, cur_lb, target, mutation);
                                };
                                inference.infer_greater_than_or_equal(logger, starts[j], target,
                                    JustifyExplicitly{justify, ThenRUP::Yes, hints::Disjunctive{owner}}, reason_over(push_reason_vars));
                            }
                        }

                        // ub-push, to the successor's latest start less j's
                        // own guaranteed duration, clipped to one below j's
                        // lower bound. cur_ub is the bound captured before
                        // any push above landed: by the time the justification
                        // runs, the state holds the pushed bound, which the
                        // reason does not support.
                        if (successor) {
                            auto target = max(successor_lst - min_len(j), cur_lb - 1_i) - (one_too_far ? 1_i : 0_i);
                            if (target < cur_ub) {
                                auto justify = [&, j, k = *successor, cur_ub, target](const ReasonLiterals & reason) -> void {
                                    logger->emit_proof_comment(
                                        "disjunctive detectable precedence " + std::to_string(j) + "<<" + std::to_string(k) + " push=ub");
                                    pin_escapes(reason, {j, k});
                                    emit_ub_dichotomy(j, k, cur_ub, target, mutation);
                                };
                                inference.infer_less_than(logger, starts[j], target + 1_i,
                                    JustifyExplicitly{justify, ThenRUP::Yes, hints::Disjunctive{owner}}, reason_over(push_reason_vars));
                            }
                        }
                    }
            }

            // Strict-mode zero-length tasks: check that no zero-length task
            // (constant 0, or a variable duration currently fixed to 0) with a
            // fixed start sits strictly inside another task's open active
            // interval, where that task has a fixed start and a fixed positive
            // duration. Non-strict mode skips this entirely: a zero-length task
            // floats freely (and the separation clause's zero escape allows it).
            //
            // The proof is JustifyUsingRUP: at this all-fixed leaf the
            // declarative pairwise encoding alone is enough. With s_z, s_k (and
            // any variable durations) fixed at vz, vk, l_k satisfying
            // vk < vz < vk + l_k, before_{z,k} = (vz <= vk) UPs to 0 and
            // before_{k,z} = (vk + l_k <= vz) UPs to 0, contradicting the
            // encoded clause before_{z,k} + before_{k,z} >= 1. With optional
            // tasks the clause carries their presence disjuncts too, so both
            // tasks must be known present for it to unit-fail --- which is also
            // the semantics: an absent task sits wherever it likes. This is the
            // second half of what makes the propagator a *checker*, so the
            // presence test here has to be the same one the profile above uses,
            // or an undecided task could slip past the leaf check that would
            // have fixed its presence.
            for (auto z : active_tasks) {
                if (! strict)
                    break;
                if (max_len(z) > 0_i)
                    continue;
                if (! state.has_single_value(starts[z]) || ! is_present(z))
                    continue;
                auto vz = state.lower_bound(starts[z]);
                for (auto k : active_tasks) {
                    // k must have a fixed, positive duration.
                    if (k == z || min_len(k) != max_len(k) || min_len(k) == 0_i)
                        continue;
                    if (! state.has_single_value(starts[k]) || ! is_present(k))
                        continue;
                    auto vk = state.lower_bound(starts[k]);
                    if (vk < vz && vz < vk + min_len(k)) {
                        auto reason_vars = starts;
                        if (is_var_len(z))
                            reason_vars.push_back(length_vars[z]);
                        if (is_var_len(k))
                            reason_vars.push_back(length_vars[k]);
                        inference.contradiction(logger, JustifyUsingRUP{hints::Disjunctive{owner}}, reason_over(reason_vars));
                        return PropagatorState::DisableUntilBacktrack;
                    }
                }
            }

            return PropagatorState::Enable;
        },
        triggers);
}

auto Disjunctive::constraint_type() const -> std::string
{
    // The optional forms are named apart from the plain ones rather than
    // sharing a name: cake_pb_cp dispatches on this, and it has no encoder for
    // an optional disjunctive, so a shared name would silently offer it the
    // non-optional encoding of a different constraint. Naming the gap is what
    // makes it a miss rather than a mismatch.
    if (_presences.empty())
        return _strict ? "disjunctive_strict" : "disjunctive";
    return _strict ? "disjunctive_strict_optional" : "disjunctive_optional";
}

auto Disjunctive::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    vector<SExpr> starts, lengths, presences;
    for (const auto & v : _starts)
        starts.push_back(tracker.s_expr_term_of(v));
    for (const auto & l : _lengths)
        lengths.push_back(is_constant_variable(l) ? SExpr::atom(constant_value_of(l).to_string()) : tracker.s_expr_term_of(l));
    for (const auto & p : _presences)
        presences.push_back(tracker.s_expr_term_of(p));
    vector<SExpr> terms{
        SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(std::move(starts)), SExpr::list(std::move(lengths))};
    // The presences list sits where the FlatZinc builtin puts it, last, and is
    // absent altogether for a non-optional constraint --- whose s-expression
    // must stay exactly what it was.
    if (! _presences.empty())
        terms.push_back(SExpr::list(std::move(presences)));
    return SExpr::list(std::move(terms));
}
