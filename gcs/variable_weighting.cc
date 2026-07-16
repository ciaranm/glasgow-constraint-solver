#include <gcs/current_state.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/variable_weighting.hh>

#include <util/overloaded.hh>

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <map>
#include <optional>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::map;
using std::max;
using std::nullopt;
using std::optional;
using std::pair;
using std::pow;
using std::size_t;
using std::unordered_map;
using std::vector;

namespace
{
    // Conflict-History Search tunables (Habet & Terrioux). These are defaults to
    // be auto-tuned, not design choices.
    constexpr double chs_alpha_initial = 0.4;
    constexpr double chs_alpha_minimum = 0.06;
    constexpr double chs_alpha_decay = 1.0e-6;
    constexpr double chs_delta = 1.0e-4;
    constexpr double chs_smoothing_base = 0.995;
}

auto WeightingState::weight_of(const ConstraintID & constraint_id) const -> double
{
    auto it = _constraint_weights.find(constraint_id);
    return it == _constraint_weights.end() ? 0.0 : it->second;
}

auto WeightingState::optional_weight_of(const ConstraintID & constraint_id) const -> optional<double>
{
    auto it = _constraint_weights.find(constraint_id);
    if (it == _constraint_weights.end())
        return nullopt;
    return it->second;
}

auto WeightingState::set_weight(const ConstraintID & constraint_id, double weight) -> void
{
    _constraint_weights[constraint_id] = weight;
}

auto WeightingState::merge(const WeightingState & other, MergePolicy policy) -> void
{
    auto combine = [policy](double & mine, double theirs) {
        switch (policy) {
            using enum MergePolicy;
        case Sum: mine += theirs; break;
        case Max: mine = max(mine, theirs); break;
        case Average: mine = (mine + theirs) / 2.0; break;
        }
    };

    for (const auto & [constraint_id, their_weight] : other._constraint_weights)
        combine(_constraint_weights[constraint_id], their_weight);
    for (const auto & [key, their_weight] : other._local_weights)
        combine(_local_weights[key], their_weight);
}

auto WeightingState::constraint_weights() const -> const unordered_map<ConstraintID, double> &
{
    return _constraint_weights;
}

auto WeightingState::local_weight_of(const ConstraintID & constraint_id, SimpleIntegerVariableID var) const -> optional<double>
{
    auto it = _local_weights.find(pair{constraint_id, var});
    if (it == _local_weights.end())
        return nullopt;
    return it->second;
}

auto WeightingState::set_local_weight(const ConstraintID & constraint_id, SimpleIntegerVariableID var, double weight) -> void
{
    _local_weights[pair{constraint_id, var}] = weight;
}

auto WeightingState::local_weights() const -> const map<pair<ConstraintID, SimpleIntegerVariableID>, double> &
{
    return _local_weights;
}

DenseConstraintWeighting::DenseConstraintWeighting(const Propagators & propagators, double default_weight) :
    _weights(propagators.number_of_constraints(), default_weight), _default_weight(default_weight)
{
}

auto DenseConstraintWeighting::contribution_of(int constraint_index) const -> double
{
    return _weights[constraint_index];
}

auto DenseConstraintWeighting::weighted_degree_of(const CurrentState & state, const Propagators & propagators, IntegerVariableID var) const -> double
{
    auto simple = overloaded{//
        [](const SimpleIntegerVariableID & v) -> optional<SimpleIntegerVariableID> { return v; },
        [](const ViewOfIntegerVariableID & v) -> optional<SimpleIntegerVariableID> { return v.actual_variable; },
        [](const ConstantIntegerVariableID &) -> optional<SimpleIntegerVariableID> {
            return nullopt;
        }}.visit(var);

    if (! simple)
        return 0.0;

    double total = 0.0;
    for (const auto & constraint_index : propagators.constraint_indices_of_variable(*simple)) {
        // Only constraints with at least two unassigned variables count; we just
        // need to know whether that threshold is met, so stop counting at two.
        int futures = 0;
        for (const auto & v : propagators.scope_of_constraint(constraint_index)) {
            if (! state.has_single_value(v))
                if (++futures >= 2)
                    break;
        }
        if (futures >= 2)
            total += contribution_of(constraint_index);
    }
    return total;
}

auto DenseConstraintWeighting::snapshot(const Propagators & propagators) const -> WeightingState
{
    WeightingState result;
    for (size_t c = 0; c < _weights.size(); ++c)
        result.set_weight(propagators.constraint_id_for_index(static_cast<int>(c)), _weights[c]);
    return result;
}

auto DenseConstraintWeighting::load(const WeightingState & state, const Propagators & propagators) -> void
{
    _weights.assign(propagators.number_of_constraints(), _default_weight);
    for (size_t c = 0; c < _weights.size(); ++c)
        if (auto weight = state.optional_weight_of(propagators.constraint_id_for_index(static_cast<int>(c))))
            _weights[c] = *weight;
}

ClassicDomWDeg::ClassicDomWDeg(const Propagators & propagators) : DenseConstraintWeighting(propagators, 1.0)
{
}

auto ClassicDomWDeg::note_conflict(int constraint_index, const vector<SimpleIntegerVariableID> &, const optional<Reason> &, const State &) -> void
{
    _weights[constraint_index] += 1.0;
}

auto ClassicDomWDeg::on_restart() -> void
{
    // Classic dom/wdeg keeps its weights across restarts; CHS-style smoothing is
    // a different scheme. Nothing to do.
}

ConflictHistorySearch::ConflictHistorySearch(const Propagators & propagators) :
    DenseConstraintWeighting(propagators, 0.0), _conflict_of(propagators.number_of_constraints(), 0), _alpha(chs_alpha_initial)
{
}

auto ConflictHistorySearch::note_conflict(int constraint_index, const vector<SimpleIntegerVariableID> &, const optional<Reason> &, const State &)
    -> void
{
    auto r = 1.0 / static_cast<double>(_number_of_conflicts - _conflict_of[constraint_index] + 1);
    _weights[constraint_index] = (1.0 - _alpha) * _weights[constraint_index] + _alpha * r;
    ++_number_of_conflicts;
    _conflict_of[constraint_index] = _number_of_conflicts;
    _alpha = max(chs_alpha_minimum, _alpha - chs_alpha_decay);
}

auto ConflictHistorySearch::contribution_of(int constraint_index) const -> double
{
    return _weights[constraint_index] + chs_delta;
}

auto ConflictHistorySearch::on_restart() -> void
{
    // Smooth scores towards 0 by their staleness, and reset alpha. Inert until
    // restarts exist (nothing calls this yet).
    for (size_t c = 0; c < _weights.size(); ++c)
        _weights[c] *= pow(chs_smoothing_base, static_cast<double>(_number_of_conflicts - _conflict_of[c]));
    _alpha = chs_alpha_initial;
}

auto ConflictHistorySearch::load(const WeightingState & state, const Propagators & propagators) -> void
{
    DenseConstraintWeighting::load(state, propagators);
    _conflict_of.assign(propagators.number_of_constraints(), 0);
    _number_of_conflicts = 0;
    _alpha = chs_alpha_initial;
}

RefinedWeighting::RefinedWeighting(const Propagators & propagators, const State & state, Variant variant) :
    _variant(variant), _local_weights(propagators.number_of_constraints())
{
    // Capture the initial domain size of every variable in a constraint scope,
    // for the InitialDomain variant.
    for (size_t c = 0; c < propagators.number_of_constraints(); ++c)
        for (const auto & v : propagators.scope_of_constraint(static_cast<int>(c)))
            _initial_domain.try_emplace(v.index, state.domain_size(v).raw_value);
}

auto RefinedWeighting::note_conflict(
    int constraint_index, const vector<SimpleIntegerVariableID> & scope, const optional<Reason> &, const State & state) -> void
{
    long long futures = 0;
    for (const auto & v : scope)
        if (! state.has_single_value(v))
            ++futures;
    if (futures == 0)
        return;

    auto & weights = _local_weights[constraint_index];
    for (const auto & x : scope) {
        if (state.has_single_value(x))
            continue;
        double increment = 0.0;
        switch (_variant) {
            using enum Variant;
        case InitialArity: increment = 1.0 / static_cast<double>(scope.size()); break;
        case CurrentArity: increment = 1.0 / static_cast<double>(futures); break;
        case InitialDomain: increment = 1.0 / static_cast<double>(_initial_domain.at(x.index)); break;
        case CurrentDomain: increment = 1.0 / (1.0 + static_cast<double>(state.domain_size(x).raw_value)); break;
        case CurrentArityCurrentDomain:
            increment = 1.0 / (static_cast<double>(futures) * (1.0 + static_cast<double>(state.domain_size(x).raw_value)));
            break;
        }
        auto [it, inserted] = weights.try_emplace(x.index, 1.0);
        it->second += increment;
    }
}

auto RefinedWeighting::weighted_degree_of(const CurrentState & state, const Propagators & propagators, IntegerVariableID var) const -> double
{
    auto simple = overloaded{//
        [](const SimpleIntegerVariableID & v) -> optional<SimpleIntegerVariableID> { return v; },
        [](const ViewOfIntegerVariableID & v) -> optional<SimpleIntegerVariableID> { return v.actual_variable; },
        [](const ConstantIntegerVariableID &) -> optional<SimpleIntegerVariableID> {
            return nullopt;
        }}.visit(var);

    if (! simple)
        return 0.0;

    double total = 0.0;
    for (const auto & constraint_index : propagators.constraint_indices_of_variable(*simple)) {
        int futures = 0;
        for (const auto & v : propagators.scope_of_constraint(constraint_index)) {
            if (! state.has_single_value(v))
                if (++futures >= 2)
                    break;
        }
        if (futures >= 2) {
            const auto & weights = _local_weights[constraint_index];
            auto it = weights.find(simple->index);
            total += (it != weights.end() ? it->second : 1.0);
        }
    }
    return total;
}

auto RefinedWeighting::on_restart() -> void
{
    // The refined increments keep their weights across restarts.
}

auto RefinedWeighting::snapshot(const Propagators & propagators) const -> WeightingState
{
    WeightingState result;
    for (size_t c = 0; c < _local_weights.size(); ++c)
        for (const auto & [var_index, weight] : _local_weights[c])
            result.set_local_weight(propagators.constraint_id_for_index(static_cast<int>(c)), SimpleIntegerVariableID{var_index}, weight);
    return result;
}

auto RefinedWeighting::load(const WeightingState & state, const Propagators & propagators) -> void
{
    for (size_t c = 0; c < _local_weights.size(); ++c) {
        _local_weights[c].clear();
        auto constraint_id = propagators.constraint_id_for_index(static_cast<int>(c));
        for (const auto & v : propagators.scope_of_constraint(static_cast<int>(c)))
            if (auto weight = state.local_weight_of(constraint_id, v))
                _local_weights[c][v.index] = *weight;
    }
}
