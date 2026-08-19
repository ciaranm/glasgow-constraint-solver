#include <gcs/constraints/disjunctive/disjunctive.hh>
#include <gcs/constraints/disjunctive/hints.hh>
#include <gcs/constraints/innards/rule_counters.hh>
#include <gcs/constraints/innards/task_presence.hh>
#include <gcs/constraints/innards/window_energy.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/am1_from_pairs.hh>
#include <gcs/innards/proofs/comparator_network.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <algorithm>
#include <bit>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <map>
#include <memory>
#include <optional>
#include <string>
#include <tuple>
#include <utility>
#include <variant>
#include <vector>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
using std::println;
#else
#include <fmt/core.h>
using fmt::println;
#endif

using namespace gcs;
using namespace gcs::innards;

using std::make_optional;
using std::make_pair;
using std::make_shared;
using std::make_tuple;
using std::make_unique;
using std::map;
using std::max;
using std::min;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::size_t;
using std::string;
using std::tuple;
using std::unique_ptr;
using std::vector;
using std::ranges::sort;

namespace
{
    /**
     * Instrumentation for the overload check (issue #730). The rule has no
     * certificate yet, so what has to be decided first is not how to write one
     * but whether one is affordable: the proof-only comparator network in the
     * issue costs O(w^3) lines for a window of w tasks --- 30k at w = 12,
     * 133k at w = 20 --- against two pols for every inference the propagator
     * makes today. Issue #731 recorded 982,065 detectable-precedence pushes in
     * a single RCPSP proof, so a comparable overload firing rate would put the
     * rule out of reach at any window size.
     *
     * Hence a static counter rather than a stats object threaded through the
     * public API: this measures a design question, and goes away with the
     * answer. Printed at exit when GCS_DISJUNCTIVE_OVERLOAD_STATS is set.
     */
    /**
     * Per-rule firing counters (#729), the sibling of the same thing in
     * `cumulative.cc`. Separate from OverloadInstrumentation below, which
     * measures what an overload *certificate* costs; these measure what each
     * rule is worth, which is a different question with a different lifetime.
     *
     * The lb and ub halves are counted apart, because measuring one half of a
     * symmetric rule and doubling has been wrong here before.
     *
     * \note Unlike `Cumulative`, edge-finding on this encoding evaluates its
     * energy condition *before* testing the live bound, so for those two rows
     * `firings + already_true` really is a detection count. For every other row
     * here, and for all of `Cumulative`, the live-bound test comes first and
     * `already_true` counts candidates rather than detections. The difference
     * is an accident of which test is cheaper on each encoding, not a
     * difference between the rules.
     */
    enum DisjunctiveRule
    {
        rule_mandatory_overlap,
        rule_time_table_lb,
        rule_time_table_ub,
        rule_presence,
        rule_detectable_precedences_lb,
        rule_detectable_precedences_ub,
        rule_edge_finding_lb,
        rule_edge_finding_ub,
        rule_not_first,
        rule_not_last,
        rule_overload,
        rule_zero_length_escape,
        rule_count
    };

    RuleInstrumentation disjunctive_counters{"disjunctive",
        {"mandatory_overlap", "time_table_lb", "time_table_ub", "presence", "detectable_precedences_lb", "detectable_precedences_ub",
            "edge_finding_lb", "edge_finding_ub", "not_first", "not_last", "overload", "zero_length_escape"}};

    struct OverloadInstrumentation
    {
        unsigned long long calls = 0, windows_examined = 0, firings = 0, declined = 0, sorted = 0;
        unsigned long long bridge_derived = 0, bridge_reused = 0;
        std::map<size_t, unsigned long long> window_sizes, candidate_counts, declined_sizes;

        ~OverloadInstrumentation()
        {
            if (! std::getenv("GCS_DISJUNCTIVE_OVERLOAD_STATS") || 0 == calls)
                return;

            auto histogram = [](const std::map<size_t, unsigned long long> & h) {
                std::string result;
                for (const auto & [k, v] : h)
                    result += (result.empty() ? "" : ",") + std::to_string(k) + "=" + std::to_string(v);
                return result;
            };

            println(std::cerr, "disjunctive_overload_calls: {}", calls);
            println(std::cerr, "disjunctive_overload_firings: {}", firings);
            println(std::cerr, "disjunctive_overload_declined: {}", declined);
            println(std::cerr, "disjunctive_overload_sorted: {}", sorted);
            println(std::cerr, "disjunctive_overload_bridge_derived: {}", bridge_derived);
            println(std::cerr, "disjunctive_overload_bridge_reused: {}", bridge_reused);
            println(std::cerr, "disjunctive_overload_windows_examined: {}", windows_examined);
            println(std::cerr, "disjunctive_overload_window_sizes: {}", histogram(window_sizes));
            println(std::cerr, "disjunctive_overload_declined_sizes: {}", histogram(declined_sizes));
            println(std::cerr, "disjunctive_overload_candidate_counts: {}", histogram(candidate_counts));
        }
    };

    OverloadInstrumentation overload_instrumentation;

    /**
     * One (task, time) flag of the overload certificate's re-encoding, and the
     * two rows defining it: `forward` is the flag implying both of its order
     * literals, `backward` the clause the two of them imply it by. The bridge
     * consumes the first and the energy telescope the second.
     */
    struct ActivityFlag
    {
        ProofFlag flag;
        /// The flag implying each of its two order literals, one clause each
        /// rather than the single row a conjunction reifies to. The bridge
        /// cancels exactly one literal per operand, so a row carrying both
        /// would leave the other behind and the pol would not close.
        ProofLine implies_starts_by, implies_started;
        /// The two of them implying the flag: what the energy sum telescopes.
        ProofLine backward;
    };
}

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
    _energy_lens.assign(n, 0_i);
    for (size_t i = 0; i < n; ++i) {
        if (is_constant_variable(_lengths[i])) {
            _length_vals[i] = constant_value_of(_lengths[i]);
            _energy_lens[i] = _length_vals[i];
        }
        else if (initial_state.lower_bound(_lengths[i]) < 0_i)
            throw InvalidProblemDefinitionException{"Disjunctive: lengths must be non-negative"};
        else
            _energy_lens[i] = initial_state.lower_bound(_lengths[i]);
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
        // Ask what big-M the reifier is about to choose, rather than assuming:
        // the sorting-network certificate raises this row to its own guard
        // coefficient, and the two directions of a pair get different constants
        // whenever their durations or encoding widths differ.
        auto guard = -model.names_and_ids_tracker().reification_shape(ineq, HalfReifyOnConjunctionOf{{flag}}).reif_coefficient;
        auto [fwd, rev] = model.add_two_way_reified_constraint(ineq, flag);
        return BeforeFlagData{flag, fwd, rev, guard};
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
        [starts = move(_starts), lengths = move(_length_vals), energy_lens = move(_energy_lens), length_vars = move(_lengths), zero = move(_zero),
            strict = _strict, active_tasks = move(_active_tasks), before_flags = move(_before_flags), clause_lines = move(_clause_lines),
            presence = move(_presence), rules = _rules, mutation = _proof_mutation, presence_mutation = _presence_mutation,
            // The overload certificate's vocabulary, kept across firings when
            // it lives at Top. A shared_ptr rather than a member because the
            // propagator is invoked through a const callable, and the cache is
            // proof-side state that no inference reads.
            activity = make_shared<map<tuple<size_t, long long, long long>, ActivityFlag>>(),
            // And the bridge's per-time at-most-ones, which depend on the same
            // three things and on nothing else, so they are reusable on exactly
            // the same terms.
            bridge = make_shared<map<tuple<size_t, size_t, long long, long long, long long>, ProofLine>>(),
            // Edge-finding's window-energy rows, on the same terms: the row is
            // a fact about the model, so it is keyed on the task, the window,
            // the two guards and the duration it was counted at, and on nothing
            // the search state can move.
            guarded = make_shared<map<tuple<size_t, long long, long long, long long, long long, long long>, window_energy::GuardedWindowEnergy>>(),
            floors = make_shared<map<size_t, ProofLine>>(), escapes = make_shared<map<size_t, ProofLine>>(),
            owner = constraint_id()](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // Current guaranteed (min) and possible (max) duration of task i:
            // for a constant duration both are the value; for a variable
            // duration they are the live lower / upper bounds.
            auto is_var_len = [&](size_t i) -> bool { return ! is_constant_variable(length_vars[i]); };
            auto min_len = [&](size_t i) -> Integer { return is_var_len(i) ? state.lower_bound(length_vars[i]) : lengths[i]; };
            // What the overload check counts, which is not the same thing: see
            // Disjunctive::_energy_lens.
            auto energy_len = [&](size_t i) -> Integer { return energy_lens[i]; };
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
            //
            // `duration_floor`, when given, replaces the duration's current
            // bound row with one the caller has: the overload certificate
            // needs a *reason-free* floor, and cites the model's declared one.
            //
            // `divisor`, when given, divides before saturating. A caller that
            // only wants the row *cited* wants it saturated at whatever degree
            // it came out with; a caller that wants to add it to something else
            // wants a clause, and saturation alone leaves the coefficients at
            // the degree rather than at one. #754 is the second kind.
            auto emit_before_pol = [&](size_t a, size_t b, const optional<IntegerVariableCondition> & cond_a,
                                       const optional<IntegerVariableCondition> & cond_b, const optional<ProofLine> & duration_floor = nullopt,
                                       const optional<Integer> & divisor = nullopt) -> ProofLine {
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
                if (duration_floor)
                    pol.add(*duration_floor);
                else if (is_var_len(a))
                    add_defining_row(length_vars[a] >= state.lower_bound(length_vars[a]));
                if (cond_b)
                    add_defining_row(*cond_b);
                if (divisor)
                    pol.divide_by(*divisor);
                return pol.saturate().emit(*logger, ProofLevel::Temporary);
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
            // --- the overload certificate's re-encoding of time --------------
            //
            // An activity flag says a task occupies a time point:
            //     act_{i,t} <-> s_i >= t - p_i + 1  AND  s_i < t + 1
            // which is a conjunction of two order literals the encoding
            // already mints, so it costs two reds and adds nothing to the
            // model. Cached when it lives at Top, its definition saying
            // nothing about the search state; the cache is cleared per firing
            // at Temporary, where backtracking deletes the rows behind it.
            //
            // The *duration* is part of the key, not just the task and the
            // time. For a constant duration that changes nothing, but a
            // variable one moves the flag's own definition, and a later firing
            // citing a flag defined at a shorter duration would be building a
            // pol whose terms no longer cancel --- a rejected proof rather than
            // an unsound one, but rejected all the same.
            // The reason-free facts a variable-duration task's bridge needs:
            // that it runs for at least its declared minimum, and --- in
            // non-strict mode, where its separation clauses carry a
            // zero-length escape --- that the escape is false. Both follow from
            // the model's own bound row, so neither wants a reason, and both
            // are about the task alone, so both are kept beside the vocabulary.
            auto duration_floor = [&](size_t i) -> optional<ProofLine> {
                if (! is_var_len(i))
                    return nullopt;
                if (auto found = floors->find(i); found != floors->end())
                    return found->second;
                return floors->emplace(i, logger->emit_rup_proof_line(WPBSum{} + 1_i * length_vars[i] >= energy_len(i), rules.overload_vocabulary_at))
                    .first->second;
            };

            auto escape_is_false = [&](size_t i) -> optional<ProofLine> {
                if (! zero[i])
                    return nullopt;
                if (auto found = escapes->find(i); found != escapes->end())
                    return found->second;
                return escapes->emplace(i, logger->emit_rup_proof_line(WPBSum{} + 1_i * ! *zero[i] >= 1_i, rules.overload_vocabulary_at))
                    .first->second;
            };

            auto activity_flag = [&](size_t i, Integer t) -> const ActivityFlag & {
                auto key = make_tuple(i, t.raw_value, energy_len(i).raw_value);
                if (auto found = activity->find(key); found != activity->end())
                    return found->second;
                auto started = starts[i] >= t - energy_len(i) + 1_i, starts_by = starts[i] < t + 1_i;
                auto both = WPBSum{} + 1_i * started + 1_i * starts_by >= 2_i;
                auto flag = logger->create_proof_flag("dovl");
                auto implies_started =
                    logger->emit_red_proof_lines_forward_reifying(WPBSum{} + 1_i * started >= 1_i, flag, rules.overload_vocabulary_at);
                auto implies_starts_by =
                    logger->emit_red_proof_lines_forward_reifying(WPBSum{} + 1_i * starts_by >= 1_i, flag, rules.overload_vocabulary_at);
                auto backward = logger->emit_red_proof_lines_reverse_reifying(both, flag, rules.overload_vocabulary_at);
                return activity->emplace(key, ActivityFlag{flag, implies_starts_by, implies_started, backward}).first->second;
            };

            // Two tasks cannot both occupy time t. This is the step
            // `Cumulative` never has to take, its OPB stating the capacity row
            // outright: here it is derived from the pairwise encoding. Each
            // direction is the before flag's [r] row plus the two operands'
            // order-literal definitions, which cancels the starts and lands on
            // degree p_x + (t - p_x + 1) - t = 1; the two directions plus the
            // separation clause pair the before literals off into a constant,
            // and halving is exact.
            //
            // Like an activity flag, the row this lands on is about a pair of
            // tasks and a time and about nothing else, so it can be kept and
            // cited again --- which is what \ref DisjunctiveRules::overload_cache_bridge
            // asks for. That turns the certificate's per-firing cost from a
            // pair of tasks per time point into a task per time point, once the
            // window's pairs have been seen; it can only pay where the
            // vocabulary is kept too, since nothing within a single firing asks
            // for the same pair and time twice.
            auto bridge_pair = [&](size_t i, size_t j, Integer t) -> ProofLine {
                if (std::holds_alternative<disjunctive_proof_mutation::RupOverloadBridge>(mutation))
                    return logger->emit_rup_proof_line(
                        WPBSum{} + 1_i * ! activity_flag(i, t).flag + 1_i * ! activity_flag(j, t).flag >= 1_i, ProofLevel::Temporary);

                auto key = make_tuple(min(i, j), max(i, j), t.raw_value, energy_len(min(i, j)).raw_value, energy_len(max(i, j)).raw_value);
                if (rules.overload_cache_bridge)
                    if (auto found = bridge->find(key); found != bridge->end()) {
                        ++overload_instrumentation.bridge_reused;
                        return found->second;
                    }

                auto half = [&](size_t x, size_t y) -> ProofLine {
                    PolBuilder pol;
                    pol.add(emit_before_pol(x, y, starts[x] >= t - energy_len(x) + 1_i, starts[y] < t + 1_i, duration_floor(x)));
                    pol.add(activity_flag(x, t).implies_started);
                    pol.add(activity_flag(y, t).implies_starts_by);
                    return pol.saturate().emit(*logger, ProofLevel::Temporary);
                };
                PolBuilder pol;
                pol.add(half(i, j));
                pol.add(half(j, i));
                pol.add(clause_lines.at(make_pair(min(i, j), max(i, j))));
                // A separation clause carrying zero-length escapes would leave
                // them in the at-most-one, where the fold has no use for them.
                for (auto r : {i, j})
                    if (auto row = escape_is_false(r))
                        pol.add(*row);
                // Kept at the vocabulary's level rather than Temporary when it
                // is to be reused. The rows it was derived from may be deleted
                // out from under it; a derivation that has already happened
                // does not need its premises to stay.
                ++overload_instrumentation.bridge_derived;
                auto line = pol.divide_by(2_i).emit(*logger, rules.overload_cache_bridge ? rules.overload_vocabulary_at : ProofLevel::Temporary);
                if (rules.overload_cache_bridge)
                    bridge->emplace(key, line);
                return line;
            };

            // The window's per-time at-most-ones: one bridge row per ordered
            // pair and time, folded by recover_am1_from_pairs. Shared between
            // the overload check and edge-finding, which want the same rows
            // over the same encoding and differ only in what they add them to.
            //
            // Every bridge first and then every fold, rather than interleaved,
            // because that is the order the overload check has always emitted
            // them in and its proofs are diffed against it.
            auto fold_at_most_ones = [&](const vector<size_t> & tasks, Integer lo, Integer hi, bool skip_fold) -> vector<ProofLine> {
                map<Integer, vector<vector<ProofLine>>> at_most_ones;
                for (Integer t = lo; t < hi; ++t) {
                    auto & tri = at_most_ones[t];
                    tri.resize(tasks.size());
                    for (size_t y = 0; y < tasks.size(); ++y)
                        for (size_t x = 0; x < y; ++x)
                            tri[y].push_back(bridge_pair(tasks[x], tasks[y], t));
                }
                vector<ProofLine> folds;
                if (skip_fold)
                    return folds;
                folds.reserve(static_cast<size_t>((hi - lo).raw_value));
                for (Integer t = lo; t < hi; ++t) {
                    vector<ProofLiteralOrFlag> members;
                    for (auto i : tasks)
                        members.push_back(activity_flag(i, t).flag);
                    folds.push_back(recover_am1_from_pairs(*logger, members, at_most_ones[t], ProofLevel::Temporary));
                }
                return folds;
            };

            // A task in the window occupies at least lb(l) of its time points.
            // Summing the backward rows telescopes --- each order literal
            // appears once positively and once negatively --- and what is left
            // over at the two ends are the p thresholds below the window,
            // which hold because the task starts inside it, and the p above,
            // which fail because it finishes inside. Both follow from bounds
            // the reason carries, so one reason-wrapped RUP each.
            auto energy_pol = [&](size_t i, Integer lo, Integer hi, const ReasonLiterals & reason) -> ProofLine {
                PolBuilder pol;
                for (Integer t = lo; t < hi; ++t)
                    pol.add(activity_flag(i, t).backward);
                for (Integer v = lo - energy_len(i) + 1_i; v <= lo; ++v)
                    pol.add(logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (starts[i] >= v) >= 1_i, ProofLevel::Temporary));
                for (Integer v = hi - energy_len(i) + 1_i; v <= hi; ++v)
                    pol.add(logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (starts[i] < v) >= 1_i, ProofLevel::Temporary));
                return pol.emit(*logger, ProofLevel::Temporary);
            };

            // A task's activity over a window, as a row that says nothing about
            // the current bounds. `energy_pol` above resolves its leftover
            // order literals against the reason, which is exactly right for the
            // overload check --- a conflict-only rule never has to keep a row
            // past the firing --- and no use at all to a rule that moves a
            // bound: edge-finding has to carry the *negated conclusion* into
            // the row, and the row has to outlive the firing to be worth
            // deriving.
            //
            // So this weakens the survivors onto two guard literals instead,
            // along the order encoding's own monotonicity, and that is
            // `derive_guarded_window_energy` --- the same lemma Cumulative's
            // energy rules cite. The two encodings differ only in where the
            // per-time row comes from: three bridges over fully reified flags
            // there, and here the reverse half of an activity flag reified
            // straight onto the two order literals, which is the same statement
            // those bridges are built to produce.
            //
            // The row range given is the window itself rather than the task's
            // possible-active interval, so the lemma does no clipping of its
            // own: unlike Cumulative's, these flags are minted on demand and
            // exist for whatever time is asked for. The clipping that does
            // happen is the one that matters --- a guard falling inside the
            // survivors' range, which is what turns a contained task's whole
            // duration into a pushed task's guaranteed overlap.
            auto guarded_energy = [&](size_t i, Integer lo, Integer hi, Integer low_guard,
                                      Integer high_guard) -> const window_energy::GuardedWindowEnergy & {
                auto key = make_tuple(i, lo.raw_value, hi.raw_value, low_guard.raw_value, high_guard.raw_value, energy_len(i).raw_value);
                if (auto found = guarded->find(key); found != guarded->end())
                    return found->second;
                const auto * simple = std::get_if<SimpleIntegerVariableID>(&starts[i]);
                if (! simple)
                    throw ProofError{"disjunctive edge-finding wants a simple start variable for task " + std::to_string(i)};
                std::function<auto(Integer)->ProofLine> row = [&](Integer t) -> ProofLine { return activity_flag(i, t).backward; };
                auto derived = window_energy::derive_guarded_window_energy(*logger,
                    window_energy::WindowRows{*simple, energy_len(i), lo, static_cast<size_t>((hi - lo).raw_value), row}, lo, hi, low_guard,
                    high_guard, rules.overload_vocabulary_at);
                if (! derived)
                    throw ProofError{"disjunctive edge-finding: task " + std::to_string(i) + " has no derivable window energy over [" +
                        std::to_string(lo.raw_value) + "," + std::to_string(hi.raw_value) + ") guarded by [" + std::to_string(low_guard.raw_value) +
                        "," + std::to_string(high_guard.raw_value) + ")"};
                return guarded->emplace(key, *derived).first->second;
            };

            // --- the overload certificate as a sorting network -----------------
            //
            // The other way to certify the same conflict: rather than
            // re-encoding time, sort the window's tasks inside the proof and
            // telescope the sorted order. Costs O(w^3) and is flat in the
            // window's span but for the wires' widths, where the time-indexed
            // route is O(w^2) per time point --- so which is cheaper is a
            // property of the window's shape, and neither dominates.
            //
            // Not every window can take it. A wire reads a start variable's own
            // bit encoding, which has to be a simple variable's and has to read
            // as an unsigned magnitude, and the durations have to be constants
            // for the separation rows to be duration-relative. A window failing
            // any of that falls back rather than declining the conflict.
            auto sorting_network_bits = [&](size_t i) -> optional<vector<ProofLiteralOrFlag>> {
                if (is_var_len(i))
                    return nullopt;
                const auto * simple = std::get_if<SimpleIntegerVariableID>(&starts[i]);
                if (! simple)
                    return nullopt;
                auto & tracker = logger->names_and_ids_tracker();
                auto bits = tracker.num_bits(*simple);
                // A negative bit sits at index zero and carries -2^(k+1), so a
                // wire reading the vector as an unsigned magnitude would be
                // reading a different number.
                if (bits > 0_i && tracker.get_bit(*simple, 0_i).first != 1_i)
                    return nullopt;
                vector<ProofLiteralOrFlag> result;
                for (Integer b = 0_i; b < bits; ++b)
                    result.push_back(ProofBitVariable{*simple, b, true});
                return result;
            };

            auto sorting_certificate_width = [&](const vector<size_t> & tasks, Integer hi) -> optional<int> {
                auto width = static_cast<int>(std::bit_width(static_cast<unsigned long long>(hi.raw_value)));
                for (auto i : tasks) {
                    auto bits = sorting_network_bits(i);
                    if (! bits)
                        return nullopt;
                    width = max(width, static_cast<int>(bits->size()));
                }
                // The network's guard coefficients are 2^width sized, so a
                // variable declared over half the Integer range --- which is
                // what an unbounded FlatZinc int gets --- would overflow them
                // long before the proof got expensive enough to care.
                return width <= 40 ? optional<int>{width} : nullopt;
            };

            auto emit_sorting_certificate = [&](const vector<size_t> & tasks, Integer lo, Integer hi, int width,
                                                const ReasonLiterals & reason) -> void {
                // Everything here is Temporary: unlike the time-indexed
                // certificate's activity flags, whose definitions say nothing
                // about the search state and so can be kept, a window's wires
                // are about the window, and backtracking is what deletes them.
                logger->emit_proof_comment("disjunctive overload by sorting network");
                ComparatorNetwork network(*logger, width, lo, hi, ProofLevel::Temporary);

                // The window is a fact about the state rather than the model,
                // so every bound the network derives from it is guarded by the
                // inference's reason, at the network's own coefficient.
                WPBSum guard;
                for (const auto & lit : reason)
                    add_term_to(guard, network.big(), ! lit);
                network.assume(guard);

                vector<ProofWire> wires;
                for (auto i : tasks)
                    wires.push_back(network.wire_over(*sorting_network_bits(i)));
                for (size_t k = 0; k < tasks.size(); ++k) {
                    network.add_task(wires[k], min_len(tasks[k]));
                    network.set_bounds(wires[k]);
                }

                auto direction = [&](size_t x, size_t y) -> ModelSeparation {
                    const auto & data = before_flags.at(make_pair(x, y));
                    return ModelSeparation{data.flag, data.forward_line, data.forward_guard_coefficient};
                };
                for (size_t a = 0; a < tasks.size(); ++a)
                    for (size_t b = a + 1; b < tasks.size(); ++b) {
                        auto i = tasks[a], j = tasks[b];
                        network.add_separation(
                            wires[a], direction(i, j), wires[b], direction(j, i), clause_lines.at(make_pair(min(i, j), max(i, j))));
                    }

                // The row this lands on says the window is at least as wide as
                // the work inside it, which the firing says it is not, so the
                // framework's closing RUP has nothing left to do.
                (void)network.sum_up(network.sort(wires));
            };

            auto pin_escapes = [&](const ReasonLiterals & reason, const vector<size_t> & tasks) -> void {
                for (auto r : tasks)
                    if (zero[r])
                        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * *zero[r] <= 0_i, ProofLevel::Temporary);
            };

            // Edge-finding's certificate: the overload check's, emitted under
            // the negated conclusion. Over the same window, the contained
            // tasks' energy plus what the pushed task must still occupy if the
            // conclusion were false, against the same per-time at-most-ones.
            // That needs more of the window than the window has.
            //
            // Every guard but one is discharged by the reason. The one left
            // standing is the negated conclusion, so what the pol lands on is
            // `bound * [conclusion] >= something positive` --- which is to say
            // the pol *derives* the conclusion rather than assuming it, and the
            // framework's wrapping RUP has only to read it off.
            //
            // Every energy row is a guarded one, so it says nothing about the
            // current bounds and is cited rather than re-derived. What a firing
            // pays is the fold, the guard discharges, and one pol.
            auto edge_finding_justification = [&](Integer a, Integer b, const vector<size_t> & inside, size_t pushed, Integer pushed_low_guard,
                                                  Integer pushed_high_guard, bool discharge_low, const char * rule = "edge-finding") {
                return [&, a, b, inside, pushed, pushed_low_guard, pushed_high_guard, discharge_low, rule](const ReasonLiterals & reason) -> void {
                    logger->emit_proof_comment("disjunctive " + string{rule} + " w=" + std::to_string(inside.size()) +
                        " span=" + std::to_string((b - a).raw_value) + (discharge_low ? " lb" : " ub"));
                    if (std::holds_alternative<disjunctive_proof_mutation::EdgeFindingEmitNothing>(mutation))
                        return;

                    auto tasks = inside;
                    tasks.push_back(pushed);
                    pin_escapes(reason, tasks);

                    // A Temporary vocabulary does not outlive the firing that
                    // made it, so what the caches hold from last time has been
                    // deleted and citing it would be citing a dead row.
                    if (ProofLevel::Top != rules.overload_vocabulary_at) {
                        activity->clear();
                        bridge->clear();
                        floors->clear();
                        escapes->clear();
                        guarded->clear();
                    }

                    for (auto i : tasks)
                        for (Integer t = a; t < b; ++t)
                            (void)activity_flag(i, t);

                    PolBuilder total;
                    for (auto line :
                        fold_at_most_ones(tasks, a, b, std::holds_alternative<disjunctive_proof_mutation::SkipEdgeFindingFold>(mutation)))
                        total.add(line);

                    auto cite = [&](size_t i, Integer low_guard, Integer high_guard, bool do_low, bool do_high) {
                        const auto & row = guarded_energy(i, a, b, low_guard, high_guard);
                        total.add(row.line);
                        // The row carries low_coeff copies of ~[s >= low_guard]
                        // and `bound` copies of [s >= high_guard]; discharging
                        // one means adding that many copies of the literal the
                        // reason refutes it with.
                        if (do_low && row.low_coeff > 0_i)
                            total.add(logger->emit_rup_proof_line_under_reason(
                                          reason, WPBSum{} + 1_i * (starts[i] >= row.low_guard) >= 1_i, ProofLevel::Temporary),
                                row.low_coeff);
                        if (do_high && row.bound > 0_i)
                            total.add(logger->emit_rup_proof_line_under_reason(
                                          reason, WPBSum{} + 1_i * (starts[i] < row.high_guard) >= 1_i, ProofLevel::Temporary),
                                row.bound);
                    };

                    // A contained task is inside the window whichever way the
                    // push goes, so the reason refutes both its guards: it
                    // starts at or after the window does, and it starts early
                    // enough to end inside it.
                    for (auto i : inside) {
                        if (std::holds_alternative<disjunctive_proof_mutation::DropContainedEnergy>(mutation) && i == inside.front())
                            continue;
                        cite(i, a, b - energy_len(i) + 1_i, true, true);
                    }
                    if (! std::holds_alternative<disjunctive_proof_mutation::DropPushedEnergy>(mutation))
                        cite(pushed, pushed_low_guard, pushed_high_guard, discharge_low, ! discharge_low);

                    total.emit(*logger, ProofLevel::Temporary);
                };
            };

            // --- #754: the set-based detectable precedence -------------------
            //
            // #734 pushes lb(s_j) to the latest single predecessor's earliest
            // end. Vilim's rule pushes to the *set's* earliest completion time
            // `ect(Omega) = max over cuts of (est(Omega') + p(Omega'))`, which
            // is larger exactly when the predecessors cannot all fit before it.
            //
            // The certificate is #757's mechanism, and both of its halves.
            // Under the negated conclusion every task in the maximising cut is
            // squeezed into a window one unit too narrow for it:
            //
            //   lb push, threshold T = est(Omega') + p(Omega'):
            //       s_j < T  and  k before j  =>  s_k < T - p_k
            //       so Omega' lies in [est(Omega'), T - 1), p(Omega') - 1 wide
            //
            //   ub push, threshold L = lst(Omega') = lct(Omega') - p(Omega'):
            //       s_j > L - p_j  and  j before k  =>  s_k >= L + 1
            //       so Omega' lies in [L + 1, lct(Omega')), p(Omega') - 1 wide
            //
            // Either way the guarded rows are the *standard contained-task*
            // ones --- guards `(a, b - p_k + 1)` over the derived window, the
            // same call edge-finding makes --- and what is new is only how one
            // of the two guards is discharged. In the lb push the low guard
            // falls to the reason (`est_k >= est(Omega')` is what a left cut
            // means) and the high one does not; in the ub push it is the other
            // way round. So the window is derived rather than enumerated, and
            // #757's is the left edge where this is the right one, or the other
            // way round for the mirror.
            //
            // `precedence_clause` is what discharges the guard the reason
            // cannot. It carries the conclusion literal along at that guard's
            // coefficient, so the conclusion accumulates across Omega' and the
            // summed pol *derives* it rather than assuming it.
            //
            // Every bound the arithmetic reads is one the *caller* captured at
            // detection time, never one read back out of `state` here. By the
            // time a justification runs, an earlier push in the same
            // propagation has landed and the state holds a bound the reason
            // does not support --- the trap the ub push below already records,
            // and it produces a rejected proof rather than a wrong one.
            struct SetTask
            {
                std::size_t task;
                Integer edge, duration, lb, ub;
            };
            auto precedence_clause = [&](const SetTask & k, std::size_t j, Integer j_lb, Integer j_ub, Integer p_j, Integer threshold, bool lb_push,
                                         const ReasonLiterals & reason) -> ProofLine {
                // 1. The detection, as a row: the ordering the rule found is
                // the one the bounds refute, and this is #734's own refutation
                // pol. Its degree is positive exactly when the precedence is
                // detectable, which is the same statement.
                //
                // Divided rather than merely saturated, because this row is
                // going to be *added* to another: saturation alone would leave
                // its coefficients at the degree.
                if (std::holds_alternative<disjunctive_proof_mutation::RupSetPrecedenceClause>(mutation)) {
                    // Can unit propagation reach the clause on its own? If it
                    // can, the pairwise pols are decoration and this rule needs
                    // no new step.
                    auto lit = lb_push ? (starts[j] >= threshold) : (starts[j] < threshold - p_j + 1_i);
                    auto other = lb_push ? (starts[k.task] < threshold - k.duration) : (starts[k.task] >= threshold + 1_i);
                    return logger->emit_rup_proof_line(WPBSum{} + 1_i * lit + 1_i * other >= 1_i, ProofLevel::Temporary);
                }

                auto [refuted_from, refuted_to] = lb_push ? pair{j, k.task} : pair{k.task, j};
                auto from_lb = lb_push ? j_lb : k.lb;
                auto to_ub = lb_push ? k.ub : j_ub;
                auto degree = lb_push ? p_j + j_lb - k.ub : k.duration + k.lb - j_ub;
                if (degree <= 0_i)
                    throw ProofError{"disjunctive set-based precedence: the ordering is not detectable"};
                PolBuilder refute;
                refute.add(
                    emit_before_pol(refuted_from, refuted_to, starts[refuted_from] >= from_lb, starts[refuted_to] < to_ub + 1_i, nullopt, degree));
                // What the divided row still carries is the two bounds the
                // reason holds, one on each task.
                if (! is_constant_variable(starts[refuted_from]))
                    refute.add(logger->emit_rup_proof_line_under_reason(
                        reason, WPBSum{} + 1_i * (starts[refuted_from] >= from_lb) >= 1_i, ProofLevel::Temporary));
                if (! is_constant_variable(starts[refuted_to]))
                    refute.add(logger->emit_rup_proof_line_under_reason(
                        reason, WPBSum{} + 1_i * (starts[refuted_to] < to_ub + 1_i) >= 1_i, ProofLevel::Temporary));
                auto refutation = refute.saturate().emit(*logger, ProofLevel::Temporary);

                // 2. The pair's separation clause then forces the other
                // ordering. A zero-length escape would survive into it, where
                // the step below has no use for it.
                PolBuilder forced;
                forced.add(clause_lines.at(make_pair(min(j, k.task), max(j, k.task))));
                forced.add(refutation);
                for (auto r : {j, k.task})
                    if (auto row = escape_is_false(r))
                        forced.add(*row);
                auto ordering = forced.saturate().emit(*logger, ProofLevel::Temporary);

                // 3. That ordering's own arithmetic, against the two
                // thresholds, cancels the starts and comes out at degree
                // exactly one --- and 4. discharging the ordering leaves the
                // two-literal clause the guarded row wants.
                PolBuilder clause;
                if (lb_push)
                    clause.add(emit_before_pol(k.task, j, starts[k.task] >= threshold - k.duration, starts[j] < threshold));
                else
                    clause.add(emit_before_pol(j, k.task, starts[j] >= threshold - p_j + 1_i, starts[k.task] < threshold + 1_i));
                clause.add(ordering);
                return clause.saturate().emit(*logger, ProofLevel::Temporary);
            };

            // One set-based push. `a` and `b` are the derived window, `omega`
            // the maximising cut, and `threshold` the bound being derived: `T`
            // for the lb push and `L` for the ub one.
            auto set_precedence_justification = [&](Integer a, Integer b, const vector<SetTask> & omega, size_t j, Integer j_lb, Integer j_ub,
                                                    Integer p_j, Integer threshold, bool lb_push) {
                return [&, a, b, omega, j, j_lb, j_ub, p_j, threshold, lb_push](const ReasonLiterals & reason) -> void {
                    logger->emit_proof_comment("disjunctive set-based detectable precedence w=" + std::to_string(omega.size()) +
                        " span=" + std::to_string((b - a).raw_value) + (lb_push ? " lb" : " ub"));
                    if (std::holds_alternative<disjunctive_proof_mutation::SetPrecedenceEmitNothing>(mutation))
                        return;

                    vector<size_t> members;
                    for (const auto & k : omega)
                        members.push_back(k.task);
                    auto tasks = members;
                    tasks.push_back(j);
                    pin_escapes(reason, tasks);

                    // As edge-finding: a Temporary vocabulary does not outlive
                    // the firing that made it, so what the caches hold has been
                    // deleted and citing it would be citing a dead row.
                    if (ProofLevel::Top != rules.overload_vocabulary_at) {
                        activity->clear();
                        bridge->clear();
                        floors->clear();
                        escapes->clear();
                        guarded->clear();
                    }

                    for (auto i : members)
                        for (Integer t = a; t < b; ++t)
                            (void)activity_flag(i, t);

                    PolBuilder total;
                    // j is not in this window, so the at-most-ones are over the
                    // cut alone --- unlike edge-finding's, whose pushed task is
                    // inside the window it argues about.
                    for (auto line :
                        fold_at_most_ones(members, a, b, std::holds_alternative<disjunctive_proof_mutation::SkipSetPrecedenceFold>(mutation)))
                        total.add(line);

                    for (const auto & k : omega) {
                        if (std::holds_alternative<disjunctive_proof_mutation::DropSetPrecedenceEnergy>(mutation) && k.task == omega.front().task)
                            continue;
                        const auto & row = guarded_energy(k.task, a, b, a, b - k.duration + 1_i);
                        total.add(row.line);
                        // The guard the reason holds, and the guard only the
                        // negated conclusion holds. Which is which is the whole
                        // difference between the two halves.
                        if (lb_push) {
                            if (row.low_coeff > 0_i)
                                total.add(logger->emit_rup_proof_line_under_reason(
                                              reason, WPBSum{} + 1_i * (starts[k.task] >= row.low_guard) >= 1_i, ProofLevel::Temporary),
                                    row.low_coeff);
                            if (row.bound > 0_i && ! std::holds_alternative<disjunctive_proof_mutation::DropSetPrecedenceClause>(mutation))
                                total.add(precedence_clause(k, j, j_lb, j_ub, p_j, threshold, true, reason), row.bound);
                        }
                        else {
                            if (row.low_coeff > 0_i && ! std::holds_alternative<disjunctive_proof_mutation::DropSetPrecedenceClause>(mutation))
                                total.add(precedence_clause(k, j, j_lb, j_ub, p_j, threshold, false, reason), row.low_coeff);
                            if (row.bound > 0_i)
                                total.add(logger->emit_rup_proof_line_under_reason(
                                              reason, WPBSum{} + 1_i * (starts[k.task] < row.high_guard) >= 1_i, ProofLevel::Temporary),
                                    row.bound);
                        }
                    }

                    total.emit(*logger, ProofLevel::Temporary);
                };
            };

            // --- #757: the published not-first / not-last condition ----------
            //
            // `not_first_not_last` above asks whether the window the sweep
            // enumerated is overfilled by the contained set plus whatever of
            // `j` must lie in it under the negated conclusion. The rule as
            // published (Baptiste, Le Pape and Nuijten; Vilim's Theta-tree
            // presentation) argues over a window the negated conclusion
            // *derives* instead:
            //
            //     p(Theta) > lct(Theta) - ect_j      not-first
            //     p(Theta) > ub(s_j) - est(Theta)    not-last, the mirror
            //
            // and the certificate follows the window. For not-first it is
            // `[ect_j, lct(Theta))`, whose *left* edge the conclusion supplies;
            // for not-last `[est(Theta), ub(s_j))`, whose *right* edge it does.
            // Either way the rows cited are the standard contained-task guarded
            // ones over that window, and what is new --- exactly as in #754,
            // whose mechanism this is --- is that one of each row's two guards
            // is discharged by a *derived two-literal clause* rather than by
            // the reason, the clause carrying the conclusion literal along at
            // that guard's coefficient so the conclusion accumulates across
            // Theta and the summed pol derives it.
            //
            // Which guard is which is the whole difference between the two
            // halves, and it is the opposite way round from #754's:
            //
            //     not-first  low guard  [s_k >= ect_j]      derived
            //                high guard [s_k < b - p_k + 1] from the reason
            //     not-last   low guard  [s_k >= est(Theta)] from the reason
            //                high guard [s_k < ub(s_j) - p_k + 1] derived
            //
            // Why the derived guard follows. Take not-first, and suppose the
            // conclusion `s_j >= ECT(Theta)` fails. Then for every k in Theta,
            // `s_j < ECT(Theta) <= ect_k = est_k + p_k <= s_k + p_k`, so k does
            // not run before j; the pair's separation clause therefore puts j
            // before k, and `s_k >= s_j + p_j >= lb(s_j) + p_j = ect_j`. Every
            // contained task is in `[ect_j, lct(Theta))`, which the detection
            // says is too narrow to hold them. The mirror reads the same
            // sentence backwards.
            //
            // As everywhere else here, every bound the arithmetic reads is one
            // the *caller* captured at detection time. By the time a
            // justification runs an earlier push has landed, and the state
            // holds a bound the reason does not support.
            struct PublishedTask
            {
                std::size_t task;
                Integer duration, lb, ub;
            };

            // The two-literal clause. `conclusion` is the threshold being
            // derived --- `[s_j >= conclusion]` for not-first and
            // `[s_j < conclusion]` for not-last --- and `edge` the guard
            // literal's own threshold, which is the derived window edge for the
            // main path and the task's own far bound for the shortcut below.
            auto published_clause = [&](const PublishedTask & k, std::size_t j, Integer j_lb, Integer j_ub, Integer p_j, Integer conclusion,
                                        Integer edge, bool not_first, const ReasonLiterals & reason) -> ProofLine {
                if (std::holds_alternative<disjunctive_proof_mutation::RupPublishedClause>(mutation)) {
                    // Can unit propagation reach the clause on its own? If it
                    // can, the pairwise pols below are decoration.
                    auto lit = not_first ? (starts[j] >= conclusion) : (starts[j] < conclusion);
                    auto other = not_first ? (starts[k.task] >= edge) : (starts[k.task] < edge);
                    return logger->emit_rup_proof_line(WPBSum{} + 1_i * lit + 1_i * other >= 1_i, ProofLevel::Temporary);
                }

                // 1. The ordering the negated conclusion rules out, refuted by
                // #734's own pol --- except that here one of the two bounds it
                // resolves against is the negated conclusion rather than the
                // reason, so that literal is *kept* rather than discharged.
                // That is the whole of what makes the window derived.
                //
                // Divided rather than merely saturated, because this row is
                // going to be added to another.
                auto [refuted_from, refuted_to] = not_first ? pair{k.task, j} : pair{j, k.task};
                auto from_lit = not_first ? (starts[k.task] >= k.lb) : (starts[j] >= conclusion);
                auto to_lit = not_first ? (starts[j] < conclusion) : (starts[k.task] < k.ub + 1_i);
                auto degree = not_first ? k.duration + k.lb - conclusion + 1_i : p_j + conclusion - k.ub;
                if (degree <= 0_i)
                    throw ProofError{"disjunctive published not-first / not-last: the negated conclusion does not refute the ordering"};
                PolBuilder refute;
                refute.add(emit_before_pol(refuted_from, refuted_to, from_lit, to_lit, nullopt, degree));
                // Only the reason's half is discharged. The conclusion's stays
                // in, and is what the guarded row will eventually be paid with.
                auto kept_side_is_from = ! not_first;
                if (! kept_side_is_from && ! is_constant_variable(starts[refuted_from]))
                    refute.add(logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * from_lit >= 1_i, ProofLevel::Temporary));
                if (kept_side_is_from && ! is_constant_variable(starts[refuted_to]))
                    refute.add(logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * to_lit >= 1_i, ProofLevel::Temporary));
                auto refutation = refute.saturate().emit(*logger, ProofLevel::Temporary);

                // 2. The pair's separation clause then forces the other
                // ordering, still carrying the conclusion literal.
                PolBuilder forced;
                forced.add(clause_lines.at(make_pair(min(j, k.task), max(j, k.task))));
                forced.add(refutation);
                for (auto r : {j, k.task})
                    if (auto row = escape_is_false(r))
                        forced.add(*row);
                auto ordering = forced.saturate().emit(*logger, ProofLevel::Temporary);

                // 3. That ordering's own arithmetic against the window edge
                // comes out at degree exactly one, and 4. discharging the
                // ordering leaves the two-literal clause the guarded row wants.
                PolBuilder clause;
                if (not_first) {
                    clause.add(emit_before_pol(j, k.task, starts[j] >= j_lb, starts[k.task] < edge));
                    if (! is_constant_variable(starts[j]))
                        clause.add(
                            logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (starts[j] >= j_lb) >= 1_i, ProofLevel::Temporary));
                }
                else {
                    clause.add(emit_before_pol(k.task, j, starts[k.task] >= edge, starts[j] < j_ub + 1_i));
                    if (! is_constant_variable(starts[j]))
                        clause.add(logger->emit_rup_proof_line_under_reason(
                            reason, WPBSum{} + 1_i * (starts[j] < j_ub + 1_i) >= 1_i, ProofLevel::Temporary));
                }
                clause.add(ordering);
                return clause.saturate().emit(*logger, ProofLevel::Temporary);
            };

            // One published-condition push. `[lo, hi)` is the derived window
            // and `omega` the contained set, whose whole duration the detection
            // says will not fit in it.
            auto published_justification = [&](Integer lo, Integer hi, const vector<PublishedTask> & omega, std::size_t j, Integer j_lb, Integer j_ub,
                                               Integer p_j, Integer conclusion, bool not_first) {
                return [&, lo, hi, omega, j, j_lb, j_ub, p_j, conclusion, not_first](const ReasonLiterals & reason) -> void {
                    logger->emit_proof_comment("disjunctive published not-" + string{not_first ? "first" : "last"} +
                        " w=" + std::to_string(omega.size()) + " span=" + std::to_string((hi - lo).raw_value));
                    if (std::holds_alternative<disjunctive_proof_mutation::PublishedEmitNothing>(mutation))
                        return;

                    // A contained task with no room for itself in the derived
                    // window needs no energy argument: its two guards are
                    // already contradictory, so the clause taken at the task's
                    // own far bound plus the reason's row for that bound is the
                    // whole derivation. This is not a corner case bolted on ---
                    // it is where the published condition fires hardest, the
                    // window being narrower than the sweep's by construction,
                    // and it is also the only place the energy path could ask
                    // the lemma for a window it cannot fill.
                    for (const auto & k : omega)
                        if (lo + k.duration > hi) {
                            auto edge = not_first ? hi - k.duration + 1_i : lo;
                            PolBuilder pol;
                            pol.add(published_clause(k, j, j_lb, j_ub, p_j, conclusion, edge, not_first, reason));
                            pol.add(logger->emit_rup_proof_line_under_reason(reason,
                                WPBSum{} + 1_i * (not_first ? (starts[k.task] < edge) : (starts[k.task] >= edge)) >= 1_i, ProofLevel::Temporary));
                            pol.saturate().emit(*logger, ProofLevel::Temporary);
                            return;
                        }

                    vector<std::size_t> members;
                    for (const auto & k : omega)
                        members.push_back(k.task);
                    auto tasks = members;
                    tasks.push_back(j);
                    pin_escapes(reason, tasks);

                    // As edge-finding: a Temporary vocabulary does not outlive
                    // the firing that made it, so what the caches hold has been
                    // deleted and citing it would be citing a dead row.
                    if (ProofLevel::Top != rules.overload_vocabulary_at) {
                        activity->clear();
                        bridge->clear();
                        floors->clear();
                        escapes->clear();
                        guarded->clear();
                    }

                    for (auto i : members)
                        for (Integer t = lo; t < hi; ++t)
                            (void)activity_flag(i, t);

                    PolBuilder total;
                    // j is not in this window --- it is what the window is
                    // derived *from* --- so the at-most-ones are over the
                    // contained set alone, as #754's are over its cut.
                    for (auto line :
                        fold_at_most_ones(members, lo, hi, std::holds_alternative<disjunctive_proof_mutation::SkipPublishedFold>(mutation)))
                        total.add(line);

                    for (const auto & k : omega) {
                        if (std::holds_alternative<disjunctive_proof_mutation::DropPublishedEnergy>(mutation) && k.task == omega.front().task)
                            continue;
                        const auto & row = guarded_energy(k.task, lo, hi, lo, hi - k.duration + 1_i);
                        total.add(row.line);
                        auto drop_clause = std::holds_alternative<disjunctive_proof_mutation::DropPublishedClause>(mutation);
                        if (not_first) {
                            if (row.low_coeff > 0_i && ! drop_clause)
                                total.add(published_clause(k, j, j_lb, j_ub, p_j, conclusion, row.low_guard, true, reason), row.low_coeff);
                            if (row.bound > 0_i)
                                total.add(logger->emit_rup_proof_line_under_reason(
                                              reason, WPBSum{} + 1_i * (starts[k.task] < row.high_guard) >= 1_i, ProofLevel::Temporary),
                                    row.bound);
                        }
                        else {
                            if (row.low_coeff > 0_i)
                                total.add(logger->emit_rup_proof_line_under_reason(
                                              reason, WPBSum{} + 1_i * (starts[k.task] >= row.low_guard) >= 1_i, ProofLevel::Temporary),
                                    row.low_coeff);
                            if (row.bound > 0_i && ! drop_clause)
                                total.add(published_clause(k, j, j_lb, j_ub, p_j, conclusion, row.high_guard, false, reason), row.bound);
                        }
                    }

                    total.emit(*logger, ProofLevel::Temporary);
                };
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
                ++disjunctive_counters[rule_mandatory_overlap].calls;
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
                        ++disjunctive_counters[rule_mandatory_overlap].contradictions;
                        inference.contradiction(
                            logger, JustifyExplicitly{justify, ThenRUP::Yes, hints::Disjunctive{owner}}, reason_over(reason_vars));
                        return PropagatorState::DisableUntilBacktrack;
                    }

                if (rules.time_table) {
                    ++disjunctive_counters[rule_time_table_lb].calls;
                    ++disjunctive_counters[rule_time_table_ub].calls;
                    ++disjunctive_counters[rule_presence].calls;
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
                            // When nothing fits anywhere, every start in the
                            // domain is blocked and so a blocker exists at
                            // cur_lb; an empty chain there is an internal
                            // inconsistency. Under ClaimOneTooFar a start does
                            // still fit, and the chain running out is the whole
                            // point, so the invariant is stated where it holds
                            // rather than gated on the mutation.
                            if (logger && chain.empty() && new_lb > cur_ub)
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

                            ++disjunctive_counters[rule_presence].firings;
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

                            ++disjunctive_counters[rule_time_table_lb].firings;
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

                            ++disjunctive_counters[rule_time_table_ub].firings;
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
                if (rules.detectable_precedences) {
                    ++disjunctive_counters[rule_detectable_precedences_lb].calls;
                    ++disjunctive_counters[rule_detectable_precedences_ub].calls;
                }
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
                        // The whole detected sets, for the set-based rule
                        // below, and only collected when something asks for
                        // them. `edge` is a predecessor's est and a successor's
                        // lct, which is what each left cut is ordered by; the
                        // bounds are captured here rather than read back out of
                        // `state` in the justification, since by then an earlier
                        // push has landed and the state holds a bound the reason
                        // does not support.
                        vector<SetTask> predecessors, successors;
                        for (auto k : active_tasks) {
                            if (k == j || min_len(k) == 0_i || ! is_present(k))
                                continue;
                            auto [k_lb, k_ub] = state.bounds(starts[k]);
                            auto eet_k = k_lb + min_len(k);
                            if (cur_lb + min_len(j) > k_ub) {
                                if (! predecessor || eet_k > predecessor_eet) {
                                    predecessor = k;
                                    predecessor_eet = eet_k;
                                }
                                if (rules.detectable_precedences_set)
                                    predecessors.push_back(SetTask{k, k_lb, min_len(k), k_lb, k_ub});
                            }
                            if (eet_k > cur_ub) {
                                if (! successor || k_ub < successor_lst) {
                                    successor = k;
                                    successor_lst = k_ub;
                                }
                                if (rules.detectable_precedences_set)
                                    successors.push_back(SetTask{k, k_ub + min_len(k), min_len(k), k_lb, k_ub});
                            }
                        }

                        // Vilim's set-based thresholds, by a left-cut scan
                        // rather than a Theta-tree. The maximum over subsets
                        // is attained at a cut --- for a candidate `a` among
                        // the ests, taking every predecessor with `est >= a`
                        // never lowers `est(Omega')` below `a` and only adds
                        // duration --- so sorting by est descending and
                        // accumulating gives it in one pass.
                        //
                        // Returns the cut as well as the threshold, since the
                        // certificate argues about the cut's own window; and
                        // nullopt where no cut beats the pairwise rule, which
                        // is what says to take #734's certificate instead.
                        struct SetCut
                        {
                            Integer threshold, edge;
                            vector<SetTask> cut;
                        };
                        auto set_ect = [&]() -> optional<SetCut> {
                            sort(predecessors, [](const auto & x, const auto & y) { return x.edge > y.edge; });
                            optional<SetCut> best;
                            Integer running = 0_i;
                            for (size_t n = 0; n < predecessors.size(); ++n) {
                                running += predecessors[n].duration;
                                auto est_k = predecessors[n].edge;
                                // Only the last of a run of equal ests is a cut:
                                // an earlier one leaves a task with the same est
                                // out of a set it belongs to.
                                if (n + 1 < predecessors.size() && predecessors[n + 1].edge == est_k)
                                    continue;
                                auto threshold = est_k + running;
                                if (threshold <= predecessor_eet || (best && threshold <= best->threshold))
                                    continue;
                                best = SetCut{threshold, est_k, vector<SetTask>{predecessors.begin(), predecessors.begin() + n + 1}};
                            }
                            return best;
                        };
                        // The mirror: `lst(Omega)` is the smallest
                        // `lct(Omega') - p(Omega')`, so sort by lct ascending.
                        auto set_lst = [&]() -> optional<SetCut> {
                            sort(successors, [](const auto & x, const auto & y) { return x.edge < y.edge; });
                            optional<SetCut> best;
                            Integer running = 0_i;
                            for (size_t n = 0; n < successors.size(); ++n) {
                                running += successors[n].duration;
                                auto lct_k = successors[n].edge;
                                if (n + 1 < successors.size() && successors[n + 1].edge == lct_k)
                                    continue;
                                auto threshold = lct_k - running;
                                if (threshold >= successor_lst || (best && threshold >= best->threshold))
                                    continue;
                                best = SetCut{threshold, lct_k, vector<SetTask>{successors.begin(), successors.begin() + n + 1}};
                            }
                            return best;
                        };

                        auto one_too_far = std::holds_alternative<disjunctive_proof_mutation::PushOneTooFar>(mutation);

                        // lb-push, to the predecessor's earliest end, clipped
                        // to one past j's upper bound: a push that wipes the
                        // domain is a contradiction, and the target has to
                        // stay somewhere the order literal exists.
                        if (predecessor) {
                            auto cut = rules.detectable_precedences_set ? set_ect() : nullopt;
                            auto pairwise_target = min(predecessor_eet, cur_ub + 1_i) + (one_too_far ? 1_i : 0_i);
                            auto target = cut ? min(cut->threshold, cur_ub + 1_i) + (one_too_far ? 1_i : 0_i) : pairwise_target;
                            // A target the domain clip caps is one #734's own
                            // justification still covers, so the set-based
                            // certificate is emitted only where the set rule
                            // actually reaches further.
                            auto set_based = target > pairwise_target;
                            if (target > cur_lb) {
                                auto p_j = min_len(j);
                                auto justify = [&, j, k = *predecessor, cur_lb, cur_ub, p_j, target, set_based, cut](
                                                   const ReasonLiterals & reason) -> void {
                                    if (set_based) {
                                        set_precedence_justification(
                                            cut->edge, cut->threshold - 1_i, cut->cut, j, cur_lb, cur_ub, p_j, cut->threshold, true)(reason);
                                        return;
                                    }
                                    logger->emit_proof_comment(
                                        "disjunctive detectable precedence " + std::to_string(k) + "<<" + std::to_string(j) + " push=lb");
                                    pin_escapes(reason, {j, k});
                                    emit_lb_dichotomy(j, k, cur_lb, target, mutation);
                                };
                                ++disjunctive_counters[rule_detectable_precedences_lb].firings;
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
                            auto cut = rules.detectable_precedences_set ? set_lst() : nullopt;
                            auto pairwise_target = max(successor_lst - min_len(j), cur_lb - 1_i) - (one_too_far ? 1_i : 0_i);
                            auto target = cut ? max(cut->threshold - min_len(j), cur_lb - 1_i) - (one_too_far ? 1_i : 0_i) : pairwise_target;
                            auto set_based = target < pairwise_target;
                            if (target < cur_ub) {
                                auto p_j = min_len(j);
                                auto justify = [&, j, k = *successor, cur_lb, cur_ub, p_j, target, set_based, cut](
                                                   const ReasonLiterals & reason) -> void {
                                    if (set_based) {
                                        set_precedence_justification(
                                            cut->threshold + 1_i, cut->edge, cut->cut, j, cur_lb, cur_ub, p_j, cut->threshold, false)(reason);
                                        return;
                                    }
                                    logger->emit_proof_comment(
                                        "disjunctive detectable precedence " + std::to_string(j) + "<<" + std::to_string(k) + " push=ub");
                                    pin_escapes(reason, {j, k});
                                    emit_ub_dichotomy(j, k, cur_ub, target, mutation);
                                };
                                ++disjunctive_counters[rule_detectable_precedences_ub].firings;
                                inference.infer_less_than(logger, starts[j], target + 1_i,
                                    JustifyExplicitly{justify, ThenRUP::Yes, hints::Disjunctive{owner}}, reason_over(push_reason_vars));
                            }
                        }
                    }

                // Overload checking, the capacity-one case of Cumulative's
                // (OC'): if the tasks that must run entirely inside a window
                // [a, b) carry more guaranteed duration than the window is
                // wide, the state is infeasible.
                //
                // Last, rather than between the overflow scan and the bound
                // pushes where Cumulative puts it, because what is being
                // measured is the *marginal* firing rate: a state the rules
                // above can already refute is not one this rule would have to
                // pay a certificate for. That costs nothing in search shape,
                // since either way the node is refuted inside the same
                // propagation fixpoint.
                //
                // Edge-finding. For a window [a, b) and the set Theta of tasks
                // it contains, a task j with one end outside that cannot fit
                // alongside Theta is pushed away from the window. At capacity
                // one the cumulative form's `rest = energy - (capacity - h_j) *
                // width` collapses to p(Theta), so the two thresholds are
                //
                //     starts inside, ends after   lb(s_j) -> a + p(Theta)
                //     ends inside, starts before  ub(s_j) -> b - p_j - p(Theta)
                //
                // and they are mirror images over the same sweep. A task with
                // *neither* end inside spans the window, and no closed form
                // pushes it: its guaranteed energy is a hump in its start
                // rather than monotone. Restricting the start to one side of a
                // threshold is what makes such a hump's minimum say something,
                // and that is not-first / not-last, below, which shares this
                // sweep and so shares its gate.
                //
                // Before the overload check rather than after it, because these
                // rules prune where that one only refutes, and a window they
                // have already emptied is not one the overload check has to pay
                // a certificate for.
                if (rules.edge_finding || rules.not_first_not_last) {
                    if (rules.edge_finding) {
                        ++disjunctive_counters[rule_edge_finding_lb].calls;
                        ++disjunctive_counters[rule_edge_finding_ub].calls;
                    }
                    if (rules.not_first_not_last) {
                        ++disjunctive_counters[rule_not_first].calls;
                        ++disjunctive_counters[rule_not_last].calls;
                    }
                    struct EdgeTask
                    {
                        size_t task;
                        Integer est, lct, duration;
                    };

                    vector<EdgeTask> candidates;
                    candidates.reserve(active_tasks.size());
                    for (auto i : active_tasks) {
                        // As for the overload check: a task with no guaranteed
                        // duration carries no energy, and one not known present
                        // might not be here to carry any.
                        if (energy_len(i) == 0_i || ! is_present(i))
                            continue;
                        auto [s_lo, s_hi] = state.bounds(starts[i]);
                        candidates.push_back(EdgeTask{i, s_lo, s_hi + energy_len(i), energy_len(i)});
                    }
                    sort(candidates, [](const EdgeTask & x, const EdgeTask & y) { return x.lct < y.lct; });

                    vector<Integer> window_starts;
                    window_starts.reserve(candidates.size());
                    for (const auto & c : candidates)
                        window_starts.push_back(c.est);
                    sort(window_starts);

                    auto reason_vars = starts;
                    for (auto i : active_tasks)
                        if (is_var_len(i))
                            reason_vars.push_back(length_vars[i]);

                    for (size_t w = 0; w < window_starts.size(); ++w) {
                        if (w > 0 && window_starts[w] == window_starts[w - 1])
                            continue;
                        auto a = window_starts[w];

                        // min_ect and max_lst are not-first / not-last's
                        // thresholds, over the same growing contained set the
                        // energy accumulates over. min_est is est(Theta), which
                        // the published not-last condition wants and which is
                        // not `a`: `a` is an est the sweep enumerates, and a
                        // task holding it need not be contained.
                        Integer energy = 0_i, min_ect = 0_i, max_lst = 0_i, min_est = 0_i;
                        vector<size_t> inside;
                        // The same set again, with the bounds the published
                        // condition's certificate argues about, and only
                        // collected when something asks for them. Captured here
                        // rather than read back out of `state` in the
                        // justification: by then an earlier push has landed and
                        // the state holds a bound the reason does not support.
                        vector<PublishedTask> inside_published;
                        for (size_t c = 0; c < candidates.size(); ++c) {
                            if (candidates[c].est < a)
                                continue;
                            energy += candidates[c].duration;
                            inside.push_back(candidates[c].task);
                            if (rules.not_first_not_last_published)
                                inside_published.push_back(PublishedTask{
                                    candidates[c].task, candidates[c].duration, candidates[c].est, candidates[c].lct - candidates[c].duration});
                            min_ect = inside.size() == 1 ? candidates[c].est + candidates[c].duration
                                                         : min(min_ect, candidates[c].est + candidates[c].duration);
                            max_lst = inside.size() == 1 ? candidates[c].lct - candidates[c].duration
                                                         : max(max_lst, candidates[c].lct - candidates[c].duration);
                            min_est = inside.size() == 1 ? candidates[c].est : min(min_est, candidates[c].est);
                            auto b = candidates[c].lct;
                            // Candidates are in lct order, so `inside` is every
                            // task the window contains only once the last of a
                            // run of equal lcts has been taken.
                            if (c + 1 < candidates.size() && candidates[c + 1].lct == b && candidates[c + 1].est >= a)
                                continue;
                            // A window its own contained tasks overload is a
                            // conflict rather than a push, and the overload
                            // check below owns it: the arithmetic here would
                            // put the threshold past the window entirely, where
                            // the pushed task's clipped energy is zero and
                            // there is nothing to certify with.
                            if (energy > b - a)
                                continue;

                            if (rules.edge_finding)
                                for (const auto & j : candidates) {
                                    if (j.lct <= b && j.est >= a)
                                        continue;
                                    auto p_j = j.duration;
                                    auto starts_inside = j.est >= a;
                                    // Neither end inside: the task spans the
                                    // window, and no closed form pushes it.
                                    // That is not-first / not-last's firing
                                    // set, and this `continue` is the whole of
                                    // it.
                                    if (starts_inside == (j.lct <= b))
                                        continue;
                                    if (! (starts_inside ? rules.edge_finding_lb : rules.edge_finding_ub))
                                        continue;

                                    auto low_guard = starts_inside ? a : b - p_j - energy + 1_i;
                                    auto high_guard = starts_inside ? a + energy : b - p_j + 1_i;
                                    // Ask the lemma for exactly what the row it
                                    // will cite establishes, rather than for the
                                    // state's own figure: the row is a model
                                    // fact, and firing on more energy than it
                                    // carries is a rejected proof rather than an
                                    // unsound push.
                                    auto clipped = window_energy::window_energy_bound(
                                        p_j, a, static_cast<size_t>((b - a).raw_value), a, b, pair{low_guard, high_guard - 1_i});
                                    if (clipped <= 0_i || energy + clipped <= b - a)
                                        continue;

                                    auto [j_lo, j_hi] = state.bounds(starts[j.task]);
                                    auto & ef_counters = disjunctive_counters[starts_inside ? rule_edge_finding_lb : rule_edge_finding_ub];
                                    if (starts_inside ? high_guard <= j_lo : low_guard - 1_i >= j_hi) {
                                        ++ef_counters.already_true;
                                        continue;
                                    }
                                    ++ef_counters.firings;

                                    auto one_too_far = std::holds_alternative<disjunctive_proof_mutation::EdgeFindingOneTooFar>(mutation);
                                    auto justify = edge_finding_justification(a, b, inside, j.task, low_guard, high_guard, starts_inside);
                                    if (starts_inside)
                                        inference.infer_greater_than_or_equal(logger, starts[j.task], one_too_far ? high_guard + 1_i : high_guard,
                                            JustifyExplicitly{justify, ThenRUP::Yes, hints::Disjunctive{owner}}, reason_over(reason_vars));
                                    else
                                        inference.infer_less_than(logger, starts[j.task], one_too_far ? low_guard - 1_i : low_guard,
                                            JustifyExplicitly{justify, ThenRUP::Yes, hints::Disjunctive{owner}}, reason_over(reason_vars));
                                }

                            // Not-first / not-last. Edge-finding asks how far a
                            // task can be pushed and answers with a closed form;
                            // this asks a different question --- can j start
                            // before every task the window contains has
                            // finished, or end after every one of them has
                            // started --- and takes its thresholds from the
                            // contained set rather than from the leftover
                            // energy.
                            //
                            // Where j has one end inside the window the two
                            // overlap, and edge-finding's threshold is the
                            // furthest an energy argument over this window can
                            // reach, so its push subsumes this one and the
                            // live-bound tests below drop the duplicate. What is
                            // new is a j that SPANS the window, which
                            // edge-finding skips: its guaranteed energy is a
                            // hump in its start rather than monotone, and
                            // restricting the start to one side of a threshold
                            // is exactly what makes the hump's minimum say
                            // something.
                            if (rules.not_first_not_last)
                                for (const auto & j : candidates) {
                                    if (j.est >= a && j.lct <= b)
                                        continue;

                                    auto p_j = j.duration;
                                    auto [s_lo, s_hi] = state.bounds(starts[j.task]);
                                    auto one_too_far = std::holds_alternative<disjunctive_proof_mutation::EdgeFindingOneTooFar>(mutation);

                                    // Not-first: refute "j starts before every
                                    // contained task has ended". The guarded
                                    // row's low guard is what the reason
                                    // discharges and its high guard is the
                                    // threshold, which is the negated
                                    // conclusion.
                                    //
                                    // Any low guard at or past the window's
                                    // start discharges every survivor the ladder
                                    // has, so where j's own lower bound is
                                    // inside the window the window's start does
                                    // just as well --- and it is a fact about
                                    // the window rather than about the search,
                                    // so the row it derives is shared with
                                    // edge-finding's rather than keyed on a
                                    // bound that moves.
                                    if (rules.not_first && min_ect <= s_lo)
                                        ++disjunctive_counters[rule_not_first].already_true;
                                    else if (rules.not_first) {
                                        // The published detection instead, over
                                        // the narrower window
                                        // [ect_j, lct(Theta)): under the
                                        // negated conclusion j is before every
                                        // contained task, so all of Theta lies
                                        // in it. Certified over that derived
                                        // window --- see `published_justification`
                                        // and DisjunctiveRules::not_first_not_last_published.
                                        if (rules.not_first_not_last_published) {
                                            auto ect_j = s_lo + p_j;
                                            if (energy > b - ect_j) {
                                                ++disjunctive_counters[rule_not_first].firings;
                                                auto justify =
                                                    published_justification(ect_j, b, inside_published, j.task, s_lo, s_hi, p_j, min_ect, true);
                                                inference.infer_greater_than_or_equal(logger, starts[j.task], one_too_far ? min_ect + 1_i : min_ect,
                                                    JustifyExplicitly{justify, ThenRUP::Yes, hints::Disjunctive{owner}}, reason_over(reason_vars));
                                            }
                                        }
                                        else {
                                            auto low_guard = min(s_lo, a);
                                            auto clipped = window_energy::window_energy_bound(
                                                p_j, a, static_cast<size_t>((b - a).raw_value), a, b, pair{low_guard, min_ect - 1_i});
                                            if (clipped > 0_i && energy + clipped > b - a) {
                                                ++disjunctive_counters[rule_not_first].firings;
                                                auto justify =
                                                    edge_finding_justification(a, b, inside, j.task, low_guard, min_ect, true, "not-first");
                                                inference.infer_greater_than_or_equal(logger, starts[j.task], one_too_far ? min_ect + 1_i : min_ect,
                                                    JustifyExplicitly{justify, ThenRUP::Yes, hints::Disjunctive{owner}}, reason_over(reason_vars));
                                            }
                                        }
                                    }

                                    // Not-last: the mirror. Refute "j ends after
                                    // every contained task has started", so the
                                    // negated conclusion lands on the low guard
                                    // and j's own upper bound is what the reason
                                    // discharges --- which, unlike not-first's,
                                    // is a bound that moves, so this row is the
                                    // one place the rule cannot share a key with
                                    // edge-finding.
                                    if (rules.not_last && max_lst - p_j >= s_hi)
                                        ++disjunctive_counters[rule_not_last].already_true;
                                    else if (rules.not_last) {
                                        auto low_guard = max_lst - p_j + 1_i;
                                        // The mirror, over [est(Theta), ub(s_j)):
                                        // under the negated conclusion every
                                        // contained task ends by s_j, so this
                                        // time it is the window's *right* edge
                                        // the conclusion supplies.
                                        if (rules.not_first_not_last_published) {
                                            if (energy > s_hi - min_est) {
                                                ++disjunctive_counters[rule_not_last].firings;
                                                auto justify = published_justification(
                                                    min_est, s_hi, inside_published, j.task, s_lo, s_hi, p_j, low_guard, false);
                                                inference.infer_less_than(logger, starts[j.task], one_too_far ? low_guard - 1_i : low_guard,
                                                    JustifyExplicitly{justify, ThenRUP::Yes, hints::Disjunctive{owner}}, reason_over(reason_vars));
                                            }
                                        }
                                        else {
                                            auto clipped = window_energy::window_energy_bound(
                                                p_j, a, static_cast<size_t>((b - a).raw_value), a, b, pair{low_guard, s_hi});
                                            if (clipped > 0_i && energy + clipped > b - a) {
                                                ++disjunctive_counters[rule_not_last].firings;
                                                auto justify =
                                                    edge_finding_justification(a, b, inside, j.task, low_guard, s_hi + 1_i, false, "not-last");
                                                inference.infer_less_than(logger, starts[j.task], one_too_far ? low_guard - 1_i : low_guard,
                                                    JustifyExplicitly{justify, ThenRUP::Yes, hints::Disjunctive{owner}}, reason_over(reason_vars));
                                            }
                                        }
                                    }
                                }
                        }
                    }
                }

                if (rules.overload) {
                    ++disjunctive_counters[rule_overload].calls;
                    // Measuring what a firing would cost means measuring the
                    // *smallest* window that refutes the state, since the
                    // certificate is cubic in it: hence the full O(n^2) sweep
                    // and a minimum over it, rather than stopping at the first
                    // conflict.
                    struct Candidate
                    {
                        size_t task;
                        Integer est, lct, duration;
                    };

                    vector<Candidate> candidates;
                    candidates.reserve(active_tasks.size());
                    for (auto i : active_tasks) {
                        // A task with no guaranteed duration carries no energy,
                        // and one not known present might not be here to carry
                        // any: counting either would manufacture a conflict.
                        if (energy_len(i) == 0_i || ! is_present(i))
                            continue;
                        auto [s_lo, s_hi] = state.bounds(starts[i]);
                        candidates.push_back(Candidate{i, s_lo, s_hi + energy_len(i), energy_len(i)});
                    }
                    sort(candidates, [](const Candidate & a, const Candidate & b) { return a.lct < b.lct; });

                    vector<Integer> window_starts;
                    window_starts.reserve(candidates.size());
                    for (const auto & c : candidates)
                        window_starts.push_back(c.est);
                    sort(window_starts);

                    ++overload_instrumentation.calls;
                    ++overload_instrumentation.candidate_counts[candidates.size()];

                    // The windows worth trying are [a, b) with a an earliest
                    // start and b a latest completion time; the tasks with
                    // est >= a and lct <= b must all fit inside. Taking the
                    // candidates in lct order makes the energy accumulate, so
                    // the sweep is quadratic, and the first b to overflow for
                    // a given a is the smallest window that does.
                    vector<size_t> smallest;
                    Integer window_lo = 0_i, window_hi = 0_i;
                    for (size_t w = 0; w < window_starts.size(); ++w) {
                        if (w > 0 && window_starts[w] == window_starts[w - 1])
                            continue;
                        auto a = window_starts[w];

                        Integer energy = 0_i;
                        vector<size_t> inside;
                        for (const auto & c : candidates) {
                            if (c.est < a)
                                continue;
                            energy += c.duration;
                            inside.push_back(c.task);
                            ++overload_instrumentation.windows_examined;
                            if (energy > c.lct - a) {
                                if (smallest.empty() || inside.size() < smallest.size()) {
                                    smallest = inside;
                                    window_lo = a;
                                    window_hi = c.lct;
                                }
                                break;
                            }
                        }
                    }

                    // A capped rule declines a conflict it cannot afford to
                    // certify. Counted before the cap is applied, so the
                    // histogram says what was on offer and not merely what was
                    // taken.
                    if (! smallest.empty()) {
                        ++overload_instrumentation.firings;
                        ++overload_instrumentation.window_sizes[smallest.size()];
                        if (0 != rules.overload_max_window && smallest.size() > rules.overload_max_window) {
                            ++overload_instrumentation.declined;
                            ++overload_instrumentation.declined_sizes[smallest.size()];
                            smallest.clear();
                        }
                    }

                    if (! smallest.empty()) {

                        // Passive mode detects and counts without acting, which
                        // answers a different question: how many nodes of
                        // *today's* search tree are overloaded. That number is
                        // an upper bound rather than a cost, since a rule that
                        // actually fired would have pruned the subtree the
                        // later firings are counted in.
                        static const bool passive = nullptr != std::getenv("GCS_DISJUNCTIVE_OVERLOAD_PASSIVE");
                        if (! passive) {
                            auto reason_vars = starts;
                            for (auto i : smallest)
                                if (is_var_len(i))
                                    reason_vars.push_back(length_vars[i]);

                            // The certificate re-encodes time inside the
                            // proof. Nothing here touches the OPB, which stays
                            // the pairwise encoding whatever the rules say:
                            // the model is the statement being verified, so a
                            // model that moved with a rule selection would be
                            // a different problem per setting.
                            auto justify = [&, tasks = smallest, lo = window_lo, hi = window_hi](const ReasonLiterals & reason) -> void {
                                logger->emit_proof_comment(
                                    "disjunctive overload w=" + std::to_string(tasks.size()) + " span=" + std::to_string((hi - lo).raw_value));
                                if (std::holds_alternative<disjunctive_proof_mutation::OverloadEmitNothing>(mutation))
                                    return;

                                pin_escapes(reason, tasks);

                                // Two certificates over the one unchanged
                                // encoding, and a crossover between them. The
                                // network is flat in the window's span where
                                // re-encoding time is linear in it, so a wide
                                // window is where it pays; a window the network
                                // cannot take falls back rather than declining
                                // the conflict, since a certificate that is
                                // merely more expensive is not a reason to lose
                                // an inference.
                                auto width = sorting_certificate_width(tasks, hi);
                                auto sort_it = false;
                                switch (rules.overload_certificate) {
                                    using enum DisjunctiveOverloadCertificate;
                                case TimeIndexed: break;
                                case SortingNetwork: sort_it = width.has_value(); break;
                                case Cheaper:
                                    sort_it =
                                        width.has_value() && (hi - lo) > Integer{static_cast<long long>(rules.overload_crossover * tasks.size())};
                                    break;
                                }

                                if (sort_it) {
                                    ++overload_instrumentation.sorted;
                                    emit_sorting_certificate(tasks, lo, hi, *width, reason);
                                    return;
                                }

                                // A Temporary vocabulary does not outlive the
                                // firing that made it, so what the cache holds
                                // from last time has been deleted and citing
                                // it would be citing a dead row.
                                if (ProofLevel::Top != rules.overload_vocabulary_at) {
                                    activity->clear();
                                    bridge->clear();
                                    floors->clear();
                                    escapes->clear();
                                }

                                // (1) The vocabulary: a flag per (task, time)
                                // saying the task occupies that time.
                                for (auto i : tasks)
                                    for (Integer t = lo; t < hi; ++t)
                                        (void)activity_flag(i, t);

                                // (2) The bridge, which is what `Cumulative`
                                // never needs: its OPB states the capacity row
                                // outright, and here it has to be derived. Per
                                // ordered pair and time, the before flag's [r]
                                // row plus the two operands' order-literal
                                // definitions cancels the starts and lands on
                                // degree p_x + (t - p_x + 1) - t = 1.
                                // (3) The fold, and (4) the energies, summed:
                                // the folds say at most one task occupies each
                                // of the window's hi - lo times, the energies
                                // say the tasks between them need more than
                                // that, and the framework's closing RUP has
                                // nothing left to do.
                                PolBuilder total;
                                for (auto line :
                                    fold_at_most_ones(tasks, lo, hi, std::holds_alternative<disjunctive_proof_mutation::SkipOverloadFold>(mutation)))
                                    total.add(line);
                                if (! std::holds_alternative<disjunctive_proof_mutation::SkipOverloadEnergy>(mutation))
                                    for (auto i : tasks)
                                        total.add(energy_pol(i, lo, hi, reason));
                                if (total.empty())
                                    return;
                                total.emit(*logger, ProofLevel::Temporary);
                            };

                            ++disjunctive_counters[rule_overload].contradictions;
                            inference.contradiction(
                                logger, JustifyExplicitly{justify, ThenRUP::Yes, hints::Disjunctive{owner}}, reason_over(reason_vars));
                            return PropagatorState::DisableUntilBacktrack;
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
                ++disjunctive_counters[rule_zero_length_escape].calls;
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
                        ++disjunctive_counters[rule_zero_length_escape].contradictions;
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
