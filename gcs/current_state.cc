#include <gcs/current_state.hh>
#include <gcs/innards/state.hh>

using namespace gcs;
using namespace gcs::innards;

using std::generator;
using std::make_optional;
using std::move;
using std::optional;
using std::string;
using std::vector;

VariableDoesNotHaveUniqueValue::VariableDoesNotHaveUniqueValue(const string & w) :
    _wat(w + " does not have a unique value")
{
}

auto VariableDoesNotHaveUniqueValue::what() const noexcept -> const char *
{
    return _wat.c_str();
}

CurrentState::CurrentState(State & state) :
    _full_state(state)
{
}

CurrentState::CurrentState(optional<State> && s) :
    _state_copy(make_unique<optional<State>>(move(s))),
    _full_state(**_state_copy)
{
}

CurrentState::~CurrentState() = default;

CurrentState::CurrentState(CurrentState &&) = default;

auto CurrentState::clone() const -> CurrentState
{
    return CurrentState{make_optional(_full_state.clone())};
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

auto CurrentState::for_each_value(const IntegerVariableID v, std::function<auto(Integer)->void> f) const -> void
{
    _full_state.for_each_value(v, f);
}

auto CurrentState::each_value(const IntegerVariableID v) const -> generator<Integer>
{
    return _full_state.each_value_mutable(v);
}

auto CurrentState::copy_of_values(const IntegerVariableID v) const -> innards::IntervalSet<Integer>
{
    return _full_state.copy_of_values(v);
}
