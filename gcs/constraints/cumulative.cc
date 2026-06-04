#include <gcs/constraints/cumulative.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <optional>
#include <sstream>
#include <utility>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::move;
using std::size_t;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

namespace
{
    auto const_value_of(const IntegerVariableID & v) -> Integer
    {
        return std::get<ConstantIntegerVariableID>(v).const_value;
    }

    auto as_constant_var_ids(const vector<Integer> & vals) -> vector<IntegerVariableID>
    {
        vector<IntegerVariableID> result;
        result.reserve(vals.size());
        for (const auto & v : vals)
            result.push_back(constant_variable(v));
        return result;
    }
}

Cumulative::Cumulative(vector<IntegerVariableID> starts, vector<IntegerVariableID> lengths,
    vector<IntegerVariableID> heights, IntegerVariableID capacity) :
    _starts(move(starts)),
    _lengths(move(lengths)),
    _heights(move(heights)),
    _capacity(capacity),
    _capacity_val(0_i)
{
    if (_starts.size() != _lengths.size() || _starts.size() != _heights.size())
        throw InvalidProblemDefinitionException{"Cumulative: starts, lengths, heights must have the same size"};
    // Constant non-negativity can be checked here. Variable lengths/heights/
    // capacity carry the modelling assumption d, r, b >= 0 (mirroring MiniZinc);
    // their domains are not available until prepare().
    if (is_constant_variable(_capacity) && const_value_of(_capacity) < 0_i)
        throw InvalidProblemDefinitionException{"Cumulative: capacity must be non-negative"};
    for (const auto & l : _lengths)
        if (is_constant_variable(l) && const_value_of(l) < 0_i)
            throw InvalidProblemDefinitionException{"Cumulative: lengths must be non-negative"};
    for (const auto & h : _heights)
        if (is_constant_variable(h) && const_value_of(h) < 0_i)
            throw InvalidProblemDefinitionException{"Cumulative: heights must be non-negative"};
}

Cumulative::Cumulative(vector<IntegerVariableID> starts, vector<Integer> lengths,
    vector<Integer> heights, Integer capacity) :
    Cumulative(move(starts), as_constant_var_ids(lengths), as_constant_var_ids(heights),
        constant_variable(capacity))
{
}

auto Cumulative::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Cumulative>(_starts, _lengths, _heights, _capacity);
}

auto Cumulative::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto Cumulative::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    auto n = _starts.size();

    // Variable lengths are not yet supported (milestone M3 lifts that);
    // reject them clearly until then. Variable heights and capacity are
    // supported.
    for (const auto & l : _lengths)
        if (! is_constant_variable(l))
            throw UnimplementedException{"Cumulative: variable lengths not yet supported"};

    // Resolve snapshots used by define_proof_model and the propagator. For a
    // variable height, _height_vals[i] is a placeholder 0 (the propagator
    // reads lb(h_i) from the state and the proof uses _contrib_vars instead);
    // _height_ub[i] is the initial upper bound, used to size the contrib var
    // and to filter tasks that can never raise the profile.
    _length_vals.clear();
    _height_vals.clear();
    _height_ub.clear();
    _length_vals.reserve(n);
    _height_vals.reserve(n);
    _height_ub.reserve(n);
    for (const auto & l : _lengths)
        _length_vals.push_back(const_value_of(l));
    for (const auto & h : _heights) {
        _height_vals.push_back(is_constant_variable(h) ? const_value_of(h) : 0_i);
        _height_ub.push_back(initial_state.upper_bound(h));
    }
    if (is_constant_variable(_capacity))
        _capacity_val = const_value_of(_capacity);

    // Tasks with length 0, or whose height can only ever be 0, never raise the
    // load profile.
    _active_tasks.reserve(n);
    for (size_t i = 0; i < n; ++i)
        if (_length_vals[i] > 0_i && _height_ub[i] > 0_i)
            _active_tasks.push_back(i);

    if (_active_tasks.empty())
        return false;

    _per_task_t_lo.assign(n, 0_i);
    _per_task_t_hi.assign(n, 0_i);
    for (auto i : _active_tasks) {
        auto [s_lo, s_hi] = initial_state.bounds(_starts[i]);
        _per_task_t_lo[i] = s_lo;
        _per_task_t_hi[i] = s_hi + _length_vals[i] - 1_i;
    }
    return true;
}

auto Cumulative::define_proof_model(ProofModel & model) -> void
{
    // Time-table OPB encoding:
    //   for each task i and each time point t in its possible-active range:
    //     before_{i,t}  ⇔  starts[i] ≤ t
    //     after_{i,t}   ⇔  starts[i] ≥ t − lengths[i] + 1
    //     active_{i,t} ⇔  before_{i,t} ∧ after_{i,t}
    //   for each time point t:
    //     Σ heights[i] · active_{i,t} ≤ capacity
    _before_flags.assign(_starts.size(), {});
    _after_flags.assign(_starts.size(), {});
    _active_flags.assign(_starts.size(), {});
    _contrib_vars.assign(_starts.size(), {});

    Integer global_lo = 0_i, global_hi = -1_i;
    bool first = true;
    for (auto i : _active_tasks) {
        auto t_lo = _per_task_t_lo[i], t_hi = _per_task_t_hi[i];
        if (first || t_lo < global_lo) global_lo = t_lo;
        if (first || t_hi > global_hi) global_hi = t_hi;
        first = false;
        for (Integer t = t_lo; t <= t_hi; ++t) {
            auto before = model.create_proof_flag_fully_reifying(
                "cumbefore", "Cumulative", "starts at or before time",
                WPBSum{} + 1_i * _starts[i] <= t);
            auto after = model.create_proof_flag_fully_reifying(
                "cumafter", "Cumulative", "not yet finished at time",
                WPBSum{} + 1_i * _starts[i] >= t - _length_vals[i] + 1_i);
            auto active = model.create_proof_flag_fully_reifying(
                "cumactive", "Cumulative", "task active at time",
                WPBSum{} + 1_i * before + 1_i * after >= 2_i);
            _before_flags[i].push_back(before);
            _after_flags[i].push_back(after);
            _active_flags[i].push_back(active);

            // For a variable height, the task's load contribution at t is the
            // product height·active, which is nonlinear. Linearise it with a
            // proof-only integer contrib in [0, ub(h)]:
            //   active   ⇒ contrib = h   (contrib − h ≥ 0 and ≤ 0)
            //   ¬active  ⇒ contrib = 0   (contrib ≤ 0; contrib ≥ 0 by domain)
            if (! is_constant_variable(_heights[i])) {
                auto contrib = model.create_proof_only_integer_variable(
                    0_i, _height_ub[i], "cumcontrib",
                    IntegerVariableProofRepresentation::Bits);
                model.add_constraint("Cumulative", "contrib >= h when active",
                    WPBSum{} + 1_i * contrib + -1_i * _heights[i] >= 0_i,
                    HalfReifyOnConjunctionOf{active});
                model.add_constraint("Cumulative", "contrib <= h when active",
                    WPBSum{} + 1_i * contrib + -1_i * _heights[i] <= 0_i,
                    HalfReifyOnConjunctionOf{active});
                model.add_constraint("Cumulative", "contrib = 0 when inactive",
                    WPBSum{} + 1_i * contrib <= 0_i,
                    HalfReifyOnConjunctionOf{! active});
                _contrib_vars[i].push_back(contrib);
            }
        }
    }

    for (Integer t = global_lo; t <= global_hi; ++t) {
        WPBSum load;
        bool any = false;
        for (auto i : _active_tasks) {
            if (t < _per_task_t_lo[i] || t > _per_task_t_hi[i])
                continue;
            auto idx = (t - _per_task_t_lo[i]).raw_value;
            if (is_constant_variable(_heights[i]))
                load += _height_vals[i] * _active_flags[i][idx];
            else
                load += 1_i * _contrib_vars[i][idx];
            any = true;
        }
        if (any) {
            // Σ heights[i]·active[i,t] ≤ capacity. When the capacity is a
            // variable, move it to the left as a (−1)·capacity term so the
            // constraint stays a single linear inequality with RHS 0.
            std::optional<ProofLine> line;
            if (is_constant_variable(_capacity))
                line = model.add_constraint("Cumulative", "load at time",
                    load <= _capacity_val);
            else
                line = model.add_constraint("Cumulative", "load at time",
                    move(load) + -1_i * _capacity <= 0_i);
            if (line)
                _capacity_lines.emplace(t, *line);
        }
    }
}

auto Cumulative::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    for (auto i : _active_tasks)
        triggers.on_bounds.emplace_back(_starts[i]);
    // A tightening of the capacity's upper bound can newly overflow the load
    // profile, so re-fire on it too (constant capacity never changes).
    if (! is_constant_variable(_capacity))
        triggers.on_bounds.emplace_back(_capacity);
    // A rise in a task's guaranteed height (lb) raises the mandatory load, so
    // re-fire on variable-height bound changes too.
    for (auto i : _active_tasks)
        if (! is_constant_variable(_heights[i]))
            triggers.on_bounds.emplace_back(_heights[i]);

    propagators.install(
        [starts = move(_starts), lengths = move(_length_vals), heights_var = move(_heights),
            capacity_var = _capacity, active_tasks = move(_active_tasks),
            before_flags = move(_before_flags), after_flags = move(_after_flags),
            active_flags = move(_active_flags), contrib_vars = move(_contrib_vars),
            capacity_lines = move(_capacity_lines), per_task_t_lo = move(_per_task_t_lo)](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // The capacity may be a variable: the load profile is infeasible
            // only when it exceeds the *largest* still-allowed capacity, so the
            // threshold for every overflow/blocked test is ub(capacity). When
            // capacity is a genuine variable its bound is part of every reason.
            auto capacity = state.upper_bound(capacity_var);

            // A height may be a variable: a task's *guaranteed* contribution to
            // the load is its smallest still-allowed height, lb(h_i). For a
            // constant height lb(h_i) is just its value. Variable heights' bounds
            // are part of every reason, and the proof uses contrib_vars.
            auto hlb = [&](size_t i) { return state.lower_bound(heights_var[i]); };
            auto h_is_var = [&](size_t i) { return ! is_constant_variable(heights_var[i]); };

            vector<IntegerVariableID> reason_vars = starts;
            if (! is_constant_variable(capacity_var))
                reason_vars.push_back(capacity_var);
            for (auto i : active_tasks)
                if (h_is_var(i))
                    reason_vars.push_back(heights_var[i]);

            // Proof helper: pin task i's guaranteed load contribution at t and
            // return a (line, coeff) pair to feed the time-table pol. For a
            // constant height that is "active = 1" scaled by the height; for a
            // variable height it is "contrib >= lb(h_i)" with coefficient 1
            // (contrib is the proof-only product h_i·active in C_t). The
            // before/after RUPs give VeriPB the units to chase active's AND-gate.
            auto pin_contributor = [&](const ReasonFunction & reason, size_t i, Integer t)
                -> std::pair<ProofLine, Integer> {
                auto fi = (t - per_task_t_lo[i]).raw_value;
                logger->emit_rup_proof_line_under_reason(reason,
                    WPBSum{} + 1_i * before_flags[i][fi] >= 1_i, ProofLevel::Temporary);
                logger->emit_rup_proof_line_under_reason(reason,
                    WPBSum{} + 1_i * after_flags[i][fi] >= 1_i, ProofLevel::Temporary);
                auto active_line = logger->emit_rup_proof_line_under_reason(reason,
                    WPBSum{} + 1_i * active_flags[i][fi] >= 1_i, ProofLevel::Temporary);
                if (! h_is_var(i))
                    return {active_line, hlb(i)};
                auto contrib_line = logger->emit_rup_proof_line_under_reason(reason,
                    WPBSum{} + 1_i * contrib_vars[i][fi] >= hlb(i), ProofLevel::Temporary);
                return {contrib_line, 1_i};
            };

            // Proof helper for the pushed task j, pinned under the EXTENDED
            // reason {reason ∧ ¬ext_lit} (ext_lit appended as a disjunct). For a
            // constant height it returns (active_j+ext_lit ≥ 1, h_j); for a
            // variable height it deposits contrib_j + lb(h_j)·ext_lit ≥ lb(h_j)
            // (vacuous when ext_lit holds, "contrib_j ≥ lb(h_j)" otherwise) and
            // returns that line with coefficient 1.
            auto pin_pushed = [&](const ReasonFunction & reason, size_t j_idx, Integer t,
                                  IntegerVariableCondition ext_lit) -> std::pair<ProofLine, Integer> {
                auto fj = (t - per_task_t_lo[j_idx]).raw_value;
                logger->emit_rup_proof_line_under_reason(reason,
                    WPBSum{} + 1_i * before_flags[j_idx][fj] + 1_i * ext_lit >= 1_i, ProofLevel::Temporary);
                logger->emit_rup_proof_line_under_reason(reason,
                    WPBSum{} + 1_i * after_flags[j_idx][fj] + 1_i * ext_lit >= 1_i, ProofLevel::Temporary);
                auto active_line = logger->emit_rup_proof_line_under_reason(reason,
                    WPBSum{} + 1_i * active_flags[j_idx][fj] + 1_i * ext_lit >= 1_i, ProofLevel::Temporary);
                if (! h_is_var(j_idx))
                    return {active_line, hlb(j_idx)};
                auto contrib_line = logger->emit_rup_proof_line_under_reason(reason,
                    WPBSum{} + 1_i * contrib_vars[j_idx][fj] + hlb(j_idx) * ext_lit >= hlb(j_idx),
                    ProofLevel::Temporary);
                return {contrib_line, 1_i};
            };

            // Time-table consistency. The mandatory part of task i is the
            // half-open interval [lst_i, eet_i) where lst_i = ub(s_i) and
            // eet_i = lb(s_i) + l_i. Summing heights over mandatory parts
            // gives the load profile. Each task's bounds are then pushed
            // away from time points where placing it would force the load
            // over capacity.

            // Determine the time window we care about: the union of every
            // task's possibly-active range. This bounds both the mandatory
            // profile and the per-task bound search.
            bool any = false;
            Integer t_lo = 0_i, t_hi = -1_i;
            for (auto i : active_tasks) {
                auto [s_lo, s_hi] = state.bounds(starts[i]);
                auto lo = s_lo, hi = s_hi + lengths[i] - 1_i;
                if (! any || lo < t_lo) t_lo = lo;
                if (! any || hi > t_hi) t_hi = hi;
                any = true;
            }
            if (! any)
                return PropagatorState::DisableUntilBacktrack;

            auto range = (t_hi - t_lo + 1_i).raw_value;
            vector<Integer> mand_load(range, 0_i);

            for (auto i : active_tasks) {
                auto lst = state.upper_bound(starts[i]);
                auto eet = state.lower_bound(starts[i]) + lengths[i];
                if (lst < eet)
                    for (Integer t = lst; t < eet; ++t)
                        mand_load[(t - t_lo).raw_value] += hlb(i);
            }

            for (auto idx = 0; idx < range; ++idx)
                if (mand_load[idx] > capacity) {
                    auto violating_t = t_lo + Integer{idx};

                    // Tasks whose mandatory part covers violating_t — the ones
                    // we'll pin to active=1 in the proof.
                    vector<size_t> contributing;
                    for (auto i : active_tasks) {
                        auto lst = state.upper_bound(starts[i]);
                        auto eet = state.lower_bound(starts[i]) + lengths[i];
                        if (lst < eet && violating_t >= lst && violating_t < eet)
                            contributing.push_back(i);
                    }

                    auto justify = [&, violating_t, contributing](const ReasonFunction & reason) -> void {
                        if (! logger) return;
                        // Pin every contributing task's guaranteed load at
                        // violating_t, then combine those lines with C_t in a
                        // single pol. The result is unsatisfiable under the
                        // reason context (the pinned loads already exceed
                        // ub(capacity)), closing the framework's wrapping RUP.
                        PolBuilder pol;
                        pol.add(capacity_lines.at(violating_t));
                        for (auto i : contributing) {
                            auto [line, coeff] = pin_contributor(reason, i, violating_t);
                            pol.add(line, coeff);
                        }
                        pol.emit(*logger, ProofLevel::Temporary);
                    };

                    inference.contradiction(logger, JustifyExplicitlyThenRUP{justify},
                        generic_reason(state, reason_vars));
                    return PropagatorState::DisableUntilBacktrack;
                }

            // One step of a bound-push proof chain: a blocked time t and the
            // tasks (≠ j) whose mandatory parts cover t. Used by both
            // lb-push and ub-push.
            struct ChainStep
            {
                Integer t;
                vector<size_t> contributing;
            };

            // Helper: emit (a)–(d) for one chain step.
            //
            // `ext_lit` is the literal added to the reason in PB form (= the
            // negation of "task j is active at t"-as-bounded-by-the-running
            // half):
            //   lb-push:  ext_lit = (s_j ≥ t + 1)
            //   ub-push:  ext_lit = (s_j ≤ t − l_j)
            //
            // `emit_intermediate` deposits ext_lit as a unit under reason —
            // needed for every step except the last (the framework's wrapping
            // RUP closes the final inference).
            auto emit_chain_step = [&](size_t j_idx, Integer t,
                                       const vector<size_t> & contributing,
                                       IntegerVariableCondition ext_lit,
                                       bool emit_intermediate,
                                       const ReasonFunction & reason) -> void {
                // (a) Pin each task i ≠ j mandatory at t under the reason, and
                // (b) pin the pushed task j under the EXTENDED reason. Then
                // (c) combine all pinned load lines with C_t in one pol. After
                // cancellation the pol is dominated by (load − capacity)·ext_lit,
                // forcing ext_lit = 1 (the new bound) under the reason context.
                PolBuilder pol;
                pol.add(capacity_lines.at(t));
                for (auto i : contributing) {
                    auto [line, coeff] = pin_contributor(reason, i, t);
                    pol.add(line, coeff);
                }
                auto [j_line, j_coeff] = pin_pushed(reason, j_idx, t, ext_lit);
                pol.add(j_line, j_coeff);
                pol.emit(*logger, ProofLevel::Temporary);

                // (d) Deposit the running-bound advance as a fact under
                // reason for the next chain step's UP.
                if (emit_intermediate)
                    logger->emit_rup_proof_line_under_reason(reason,
                        WPBSum{} + 1_i * ext_lit >= 1_i, ProofLevel::Temporary);
            };

            for (auto j : active_tasks) {
                auto [cur_lb, cur_ub] = state.bounds(starts[j]);
                if (cur_lb == cur_ub)
                    continue;

                auto lst_j = cur_ub, eet_j = cur_lb + lengths[j];
                auto fits_at = [&](Integer s) -> bool {
                    for (Integer t = s; t < s + lengths[j]; ++t) {
                        auto load = mand_load[(t - t_lo).raw_value];
                        if (lst_j < eet_j && t >= lst_j && t < eet_j)
                            load -= hlb(j);
                        if (load + hlb(j) > capacity)
                            return false;
                    }
                    return true;
                };

                auto is_blocked_at = [&](Integer t) -> bool {
                    auto load = mand_load[(t - t_lo).raw_value];
                    if (lst_j < eet_j && t >= lst_j && t < eet_j)
                        load -= hlb(j);
                    return load + hlb(j) > capacity;
                };

                auto contributors_at = [&](Integer t) -> vector<size_t> {
                    vector<size_t> result;
                    for (auto i : active_tasks) {
                        if (i == j) continue;
                        auto lst_i = state.upper_bound(starts[i]);
                        auto eet_i = state.lower_bound(starts[i]) + lengths[i];
                        if (lst_i < eet_i && t >= lst_i && t < eet_i)
                            result.push_back(i);
                    }
                    return result;
                };

                // lb-push: find smallest s with fits_at(s), then chain
                // through blocked t's picking the LARGEST in each step's
                // window so the bound advances as far as possible per step.
                auto new_lb = cur_lb;
                while (new_lb <= cur_ub && ! fits_at(new_lb))
                    ++new_lb;
                if (new_lb > cur_lb) {
                    vector<ChainStep> chain;
                    Integer running_bound = cur_lb;
                    while (running_bound < new_lb) {
                        bool found = false;
                        for (Integer t = running_bound + lengths[j] - 1_i; t >= running_bound; --t)
                            if (is_blocked_at(t)) {
                                chain.push_back(ChainStep{t, contributors_at(t)});
                                running_bound = t + 1_i;
                                found = true;
                                break;
                            }
                        if (! found) break;
                    }

                    auto justify = [&, j, chain](const ReasonFunction & reason) -> void {
                        if (! logger) return;
                        for (size_t step = 0; step < chain.size(); ++step)
                            emit_chain_step(j, chain[step].t, chain[step].contributing,
                                starts[j] > chain[step].t,
                                step + 1 < chain.size(), reason);
                    };

                    inference.infer_greater_than_or_equal(logger, starts[j], new_lb,
                        JustifyExplicitlyThenRUP{justify},
                        generic_reason(state, reason_vars));
                }

                // ub-push: mirror image. Pick SMALLEST blocked t in each
                // step's window so the upper bound drops the most. Each
                // step turns a blocked t into the fact s_j ≤ t − l_j.
                auto new_ub = cur_ub;
                while (new_ub >= cur_lb && ! fits_at(new_ub))
                    --new_ub;
                if (new_ub < cur_ub) {
                    vector<ChainStep> chain;
                    Integer running_bound = cur_ub;
                    while (running_bound > new_ub) {
                        bool found = false;
                        for (Integer t = running_bound; t <= running_bound + lengths[j] - 1_i; ++t)
                            if (is_blocked_at(t)) {
                                chain.push_back(ChainStep{t, contributors_at(t)});
                                running_bound = t - lengths[j];
                                found = true;
                                break;
                            }
                        if (! found) break;
                    }

                    auto justify = [&, j, chain](const ReasonFunction & reason) -> void {
                        if (! logger) return;
                        for (size_t step = 0; step < chain.size(); ++step)
                            emit_chain_step(j, chain[step].t, chain[step].contributing,
                                starts[j] < chain[step].t - lengths[j] + 1_i,
                                step + 1 < chain.size(), reason);
                    };

                    inference.infer_less_than(logger, starts[j], new_ub + 1_i,
                        JustifyExplicitlyThenRUP{justify},
                        generic_reason(state, reason_vars));
                }
            }

            return PropagatorState::Enable;
        },
        triggers);
}

auto Cumulative::s_exprify(const ProofModel * const model) const -> string
{
    stringstream s;
    print(s, "{} cumulative (", _name);
    for (const auto & v : _starts)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(v));
    print(s, " ) ( ");
    for (const auto & l : _lengths)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(l));
    print(s, " ) ( ");
    for (const auto & h : _heights)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(h));
    print(s, " ) {}", model->names_and_ids_tracker().s_expr_name_of(_capacity));
    return s.str();
}
