#include <gcs/constraints/cumulative.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

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

Cumulative::Cumulative(vector<IntegerVariableID> starts, vector<Integer> lengths,
    vector<Integer> heights, Integer capacity) :
    _starts(move(starts)),
    _lengths(move(lengths)),
    _heights(move(heights)),
    _capacity(capacity)
{
    if (_starts.size() != _lengths.size() || _starts.size() != _heights.size())
        throw UnexpectedException{"Cumulative: starts, lengths, heights must have the same size"};
    if (_capacity < 0_i)
        throw UnexpectedException{"Cumulative: capacity must be non-negative"};
    for (auto & l : _lengths)
        if (l < 0_i)
            throw UnexpectedException{"Cumulative: lengths must be non-negative"};
    for (auto & h : _heights)
        if (h < 0_i)
            throw UnexpectedException{"Cumulative: heights must be non-negative"};
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
    // Tasks with length 0 or height 0 never raise the load profile.
    auto n = _starts.size();
    _active_tasks.reserve(n);
    for (size_t i = 0; i < n; ++i)
        if (_lengths[i] > 0_i && _heights[i] > 0_i)
            _active_tasks.push_back(i);

    if (_active_tasks.empty())
        return false;

    _per_task_t_lo.assign(n, 0_i);
    _per_task_t_hi.assign(n, 0_i);
    for (auto i : _active_tasks) {
        auto [s_lo, s_hi] = initial_state.bounds(_starts[i]);
        _per_task_t_lo[i] = s_lo;
        _per_task_t_hi[i] = s_hi + _lengths[i] - 1_i;
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
                WPBSum{} + 1_i * _starts[i] >= t - _lengths[i] + 1_i);
            auto active = model.create_proof_flag_fully_reifying(
                "cumactive", "Cumulative", "task active at time",
                WPBSum{} + 1_i * before + 1_i * after >= 2_i);
            _before_flags[i].push_back(before);
            _after_flags[i].push_back(after);
            _active_flags[i].push_back(active);
        }
    }

    for (Integer t = global_lo; t <= global_hi; ++t) {
        WPBSum load;
        bool any = false;
        for (auto i : _active_tasks) {
            if (t < _per_task_t_lo[i] || t > _per_task_t_hi[i])
                continue;
            auto idx = (t - _per_task_t_lo[i]).raw_value;
            load += _heights[i] * _active_flags[i][idx];
            any = true;
        }
        if (any) {
            auto line = model.add_constraint("Cumulative", "load at time",
                load <= _capacity);
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

    propagators.install(
        [starts = move(_starts), lengths = move(_lengths), heights = move(_heights),
            capacity = _capacity, active_tasks = move(_active_tasks),
            before_flags = move(_before_flags), after_flags = move(_after_flags),
            active_flags = move(_active_flags), capacity_lines = move(_capacity_lines),
            per_task_t_lo = move(_per_task_t_lo)](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // Time-table consistency. The mandatory part of task i is the
            // half-open interval [lst_i, eet_i) where lst_i = ub(s_i) and
            // eet_i = lb(s_i) + l_i. Summing heights over mandatory parts
            // gives the load profile. Each task's bounds are then pushed
            // away from time points where placing it would force the load
            // over capacity.
            //
            // Justifications are stubbed with AssertRatherThanJustifying:
            // proof logging for this algorithm comes in a later stage.

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
                        mand_load[(t - t_lo).raw_value] += heights[i];
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
                        // For each contributing task: RUP before=1, then
                        // after=1, then active=1. VeriPB UP can't chase
                        // through the AND-gate of `active` in one step; the
                        // intermediate before/after units give it the unit
                        // facts it needs to close the reverse-half of
                        // `active`'s reification.
                        //
                        // Once every contributing active=1 line exists, a
                        // pol line combines C_t with the scaled assertions
                        // to produce a constraint that's unsatisfiable
                        // under the reason context, closing the framework's
                        // wrapping RUP step.
                        vector<ProofLine> active_lines;
                        for (auto i : contributing) {
                            auto fi = (violating_t - per_task_t_lo[i]).raw_value;
                            logger->emit_rup_proof_line_under_reason(reason,
                                WPBSum{} + 1_i * before_flags[i][fi] >= 1_i,
                                ProofLevel::Temporary);
                            logger->emit_rup_proof_line_under_reason(reason,
                                WPBSum{} + 1_i * after_flags[i][fi] >= 1_i,
                                ProofLevel::Temporary);
                            auto line = logger->emit_rup_proof_line_under_reason(reason,
                                WPBSum{} + 1_i * active_flags[i][fi] >= 1_i,
                                ProofLevel::Temporary);
                            active_lines.push_back(line);
                        }
                        stringstream pol;
                        pol << "pol " << capacity_lines.at(violating_t);
                        for (size_t k = 0; k < contributing.size(); ++k)
                            pol << " " << active_lines[k] << " " << heights[contributing[k]].raw_value << " * +";
                        pol << " ;";
                        logger->emit_proof_line(pol.str(), ProofLevel::Temporary);
                    };

                    inference.contradiction(logger, JustifyExplicitlyThenRUP{justify},
                        generic_reason(state, starts));
                    return PropagatorState::DisableUntilBacktrack;
                }

            for (auto j : active_tasks) {
                auto [cur_lb, cur_ub] = state.bounds(starts[j]);
                if (cur_lb == cur_ub)
                    continue;

                auto lst_j = cur_ub, eet_j = cur_lb + lengths[j];
                auto fits_at = [&](Integer s) -> bool {
                    for (Integer t = s; t < s + lengths[j]; ++t) {
                        auto load = mand_load[(t - t_lo).raw_value];
                        if (lst_j < eet_j && t >= lst_j && t < eet_j)
                            load -= heights[j];
                        if (load + heights[j] > capacity)
                            return false;
                    }
                    return true;
                };

                auto new_lb = cur_lb;
                while (new_lb <= cur_ub && ! fits_at(new_lb))
                    ++new_lb;
                if (new_lb > cur_lb)
                    inference.infer_greater_than_or_equal(logger, starts[j], new_lb,
                        AssertRatherThanJustifying{},
                        generic_reason(state, starts));

                auto new_ub = cur_ub;
                while (new_ub >= cur_lb && ! fits_at(new_ub))
                    --new_ub;
                if (new_ub < cur_ub)
                    inference.infer_less_than(logger, starts[j], new_ub + 1_i,
                        AssertRatherThanJustifying{},
                        generic_reason(state, starts));
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
        print(s, " {}", l);
    print(s, " ) ( ");
    for (const auto & h : _heights)
        print(s, " {}", h);
    print(s, " ) {}", _capacity);
    return s.str();
}
