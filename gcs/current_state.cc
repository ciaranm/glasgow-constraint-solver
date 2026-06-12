#include <gcs/current_state.hh>
#include <gcs/innards/state.hh>

using namespace gcs;
using namespace gcs::innards;

using std::generator;
using std::make_unique;
using std::move;
using std::string;
using std::vector;

VariableDoesNotHaveUniqueValue::VariableDoesNotHaveUniqueValue(const string & w) :
    MessageException(w + " does not have a unique value")
{
}

CurrentState::CurrentState(State & state) :
    _full_state(state)
{
}

CurrentState::CurrentState(State && s) :
    _state_copy(make_unique<State>(move(s))),
    _full_state(*_state_copy)
{
}

CurrentState::~CurrentState() = default;

CurrentState::CurrentState(CurrentState &&) = default;

auto CurrentState::clone() const -> CurrentState
{
    return CurrentState{_full_state.clone()};
}

auto CurrentState::operator()(const IntegerVariableID & v) const -> Integer
{
    return _full_state(v);
}

auto CurrentState::operator()(const vector<IntegerVariableID> & vec) const -> vector<Integer>
{
    vector<Integer> result;
    for (auto & v : vec)
        result.push_back((*this)(v));
    return result;
}

auto CurrentState::has_single_value(const IntegerVariableID v) const -> bool
{
    return _full_state.has_single_value(v);
}

auto CurrentState::domain_size(const IntegerVariableID v) const -> Integer
{
    return _full_state.domain_size(v);
}

auto CurrentState::lower_bound(const IntegerVariableID v) const -> Integer
{
    return _full_state.lower_bound(v);
}

auto CurrentState::upper_bound(const IntegerVariableID v) const -> Integer
{
    return _full_state.upper_bound(v);
}

auto CurrentState::in_domain(const IntegerVariableID v, Integer n) const -> bool
{
    return _full_state.in_domain(v, n);
}

auto CurrentState::each_value(const IntegerVariableID v) const -> generator<Integer>
{
    return _full_state.each_value_mutable(v);
}

auto CurrentState::each_value_reversed(const IntegerVariableID v) const -> generator<Integer>
{
    return [](innards::IntervalSet<Integer> values) -> generator<Integer> {
        for (auto i : values.each_reversed())
            co_yield i;
    }(_full_state.copy_of_values(v));
}

auto CurrentState::copy_of_values(const IntegerVariableID v) const -> innards::IntervalSet<Integer>
{
    return _full_state.copy_of_values(v);
}
