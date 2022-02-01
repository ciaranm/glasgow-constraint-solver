/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/current_state.hh>
#include <gcs/detail/state.hh>

using namespace gcs;

using std::string;

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

auto CurrentState::operator()(const IntegerVariableID & v) const -> Integer
{
    return _full_state(v);
}

auto CurrentState::has_single_value(const IntegerVariableID v) const -> bool
{
    return _full_state.has_single_value(v);
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

