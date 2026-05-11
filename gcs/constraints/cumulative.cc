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
    struct TaskActivity
    {
        vector<ProofFlag> active_per_time; // indexed by t − _per_task_t_lo[i]
    };
    vector<TaskActivity> task_activity(_starts.size());

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
            task_activity[i].active_per_time.push_back(active);
        }
    }

    for (Integer t = global_lo; t <= global_hi; ++t) {
        WPBSum load;
        bool any = false;
        for (auto i : _active_tasks) {
            if (t < _per_task_t_lo[i] || t > _per_task_t_hi[i])
                continue;
            auto idx = (t - _per_task_t_lo[i]).raw_value;
            load += _heights[i] * task_activity[i].active_per_time[idx];
            any = true;
        }
        if (any)
            model.add_constraint("Cumulative", "load at time",
                load <= _capacity);
    }
}

auto Cumulative::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    for (auto i : _active_tasks)
        triggers.on_instantiated.emplace_back(_starts[i]);

    propagators.install(
        [starts = move(_starts), lengths = move(_lengths), heights = move(_heights),
            capacity = _capacity, active_tasks = move(_active_tasks)](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            // Only fire once every active task has a fixed start.
            for (auto i : active_tasks)
                if (! state.has_single_value(starts[i]))
                    return PropagatorState::Enable;

            // The load profile only changes at task start points, so checking
            // the load at every active task's start time is enough.
            for (auto i : active_tasks) {
                auto t = state.lower_bound(starts[i]);
                Integer load = 0_i;
                for (auto j : active_tasks) {
                    auto sj = state.lower_bound(starts[j]);
                    if (sj <= t && t < sj + lengths[j])
                        load += heights[j];
                }
                if (load > capacity) {
                    inference.contradiction(logger, JustifyUsingRUP{},
                        generic_reason(state, starts));
                    return PropagatorState::DisableUntilBacktrack;
                }
            }

            return PropagatorState::DisableUntilBacktrack;
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
