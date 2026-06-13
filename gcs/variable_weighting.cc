#include <gcs/current_state.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/variable_weighting.hh>

#include <util/overloaded.hh>

#include <algorithm>
#include <cstddef>
#include <optional>

using namespace gcs;
using namespace gcs::innards;

using std::max;
using std::nullopt;
using std::optional;
using std::size_t;
using std::unordered_map;
using std::vector;

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
    for (const auto & [constraint_id, their_weight] : other._constraint_weights) {
        auto & my_weight = _constraint_weights[constraint_id];
        switch (policy) {
            using enum MergePolicy;
        case Sum:
            my_weight += their_weight;
            break;
        case Max:
            my_weight = max(my_weight, their_weight);
            break;
        case Average:
            my_weight = (my_weight + their_weight) / 2.0;
            break;
        }
    }
}

auto WeightingState::constraint_weights() const -> const unordered_map<ConstraintID, double> &
{
    return _constraint_weights;
}

ClassicDomWDeg::ClassicDomWDeg(const Propagators & propagators) :
    _weights(propagators.number_of_constraints(), 1.0)
{
}

auto ClassicDomWDeg::note_conflict(int constraint_index, const vector<SimpleIntegerVariableID> &,
    const optional<ReasonFunction> &, const State &) -> void
{
    _weights[constraint_index] += 1.0;
}

auto ClassicDomWDeg::weighted_degree_of(const CurrentState & state, const Propagators & propagators,
    IntegerVariableID var) const -> double
{
    auto simple = overloaded{
        [](const SimpleIntegerVariableID & v) -> optional<SimpleIntegerVariableID> { return v; },
        [](const ViewOfIntegerVariableID & v) -> optional<SimpleIntegerVariableID> { return v.actual_variable; },
        [](const ConstantIntegerVariableID &) -> optional<SimpleIntegerVariableID> { return nullopt; }}
                      .visit(var);

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
            total += _weights[constraint_index];
    }
    return total;
}

auto ClassicDomWDeg::on_restart() -> void
{
    // Classic dom/wdeg keeps its weights across restarts; CHS-style smoothing is
    // a different scheme. Nothing to do.
}

auto ClassicDomWDeg::snapshot(const Propagators & propagators) const -> WeightingState
{
    WeightingState result;
    for (size_t c = 0; c < _weights.size(); ++c)
        result.set_weight(propagators.constraint_id_for_index(static_cast<int>(c)), _weights[c]);
    return result;
}

auto ClassicDomWDeg::load(const WeightingState & state, const Propagators & propagators) -> void
{
    _weights.assign(propagators.number_of_constraints(), 1.0);
    for (size_t c = 0; c < _weights.size(); ++c)
        if (auto weight = state.optional_weight_of(propagators.constraint_id_for_index(static_cast<int>(c))))
            _weights[c] = *weight;
}
