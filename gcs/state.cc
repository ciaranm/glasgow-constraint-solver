/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/state.hh>

#include "util/generalise.hh"
#include "util/overloaded.hh"

#include <algorithm>
#include <list>
#include <map>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

using namespace gcs;

using std::cmp_less;
using std::decay_t;
using std::find;
using std::function;
using std::get;
using std::get_if;
using std::is_same_v;
using std::list;
using std::make_optional;
using std::make_shared;
using std::map;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
using std::string;
using std::to_string;
using std::variant;
using std::vector;
using std::visit;

VariableDoesNotHaveUniqueValue::VariableDoesNotHaveUniqueValue(const string & w) :
    _wat(w + " does not have a unique value")
{
}

auto VariableDoesNotHaveUniqueValue::what() const noexcept -> const char *
{
    return _wat.c_str();
}

auto gcs::increase_inference_to(Inference & current, const Inference updated) -> void
{
    switch (updated) {
    case Inference::NoChange: break;
    case Inference::Change:
        if (current != Inference::Contradiction)
            current = updated;
        break;
    case Inference::Contradiction:
        current = updated;
        break;
    }
}

struct State::Imp
{
    const Problem * const problem;

    list<vector<IntegerVariableState>> integer_variable_states;
    list<vector<function<auto()->void>>> on_backtracks;
    map<SimpleIntegerVariableID, HowChanged> changed;
    vector<Literal> guesses;

    Imp(const Problem * const p) :
        problem(p)
    {
    }
};

State::State(const Problem * const problem) :
    _imp(new Imp{problem})
{
    _imp->integer_variable_states.emplace_back();
    _imp->on_backtracks.emplace_back();
}

State::State(State && other) noexcept = default;

State::~State() = default;

auto State::clone() const -> State
{
    State result(_imp->problem);
    result._imp->integer_variable_states = _imp->integer_variable_states;
    result._imp->on_backtracks = _imp->on_backtracks;
    result._imp->changed = _imp->changed;
    return result;
}

auto State::create_integer_variable(Integer lower, Integer upper) -> SimpleIntegerVariableID
{
    if (lower == upper)
        _imp->integer_variable_states.back().push_back(IntegerVariableConstantState{lower});
    else
        _imp->integer_variable_states.back().push_back(IntegerVariableRangeState{lower, upper});

    return SimpleIntegerVariableID{_imp->integer_variable_states.back().size() - 1};
}

auto State::create_pseudovariable(Integer lower, Integer upper, const optional<string> & name) -> SimpleIntegerVariableID
{
    auto result = create_integer_variable(lower, upper);
    if (_imp->problem->optional_proof())
        _imp->problem->optional_proof()->create_pseudovariable(result, lower, upper, name);
    return result;
}

auto State::assign_to_state_of(const DirectIntegerVariableID i) -> IntegerVariableState &
{
    return overloaded{
        [&](const SimpleIntegerVariableID & v) -> IntegerVariableState & {
            return _imp->integer_variable_states.back()[v.index];
        },
        [&](const ConstantIntegerVariableID &) -> IntegerVariableState & {
            throw UnexpectedException{"shouldn't have a const here"};
        }}
        .visit(i);
}

auto State::state_of(const DirectIntegerVariableID i, IntegerVariableState & space) -> IntegerVariableState &
{
    return overloaded{
        [&](const SimpleIntegerVariableID & v) -> IntegerVariableState & {
            return _imp->integer_variable_states.back()[v.index];
        },
        [&](const ConstantIntegerVariableID & v) -> IntegerVariableState & {
            space = IntegerVariableConstantState{v.const_value};
            return space;
        }}
        .visit(i);
}

auto State::state_of(const DirectIntegerVariableID i, IntegerVariableState & space) const -> const IntegerVariableState &
{
    return overloaded{
        [&](const SimpleIntegerVariableID & v) -> const IntegerVariableState & {
            return _imp->integer_variable_states.back()[v.index];
        },
        [&](const ConstantIntegerVariableID & v) -> const IntegerVariableState & {
            space = IntegerVariableConstantState{v.const_value};
            return space;
        }}
        .visit(i);
}

auto State::infer_literal_from_direct_integer_variable(
    const DirectIntegerVariableID var,
    LiteralFromIntegerVariable::Operator state,
    Integer value) -> pair<Inference, HowChanged>
{
    IntegerVariableState space = IntegerVariableConstantState{0_i};

    switch (state) {
        using enum LiteralFromIntegerVariable::Operator;
    case Equal:
        // Has to be equal. If the value isn't in the domain, we've found a
        // contradiction, otherwise update to a constant value.
        if (! in_domain(generalise<IntegerVariableID>(var), value))
            return pair{Inference::Contradiction, HowChanged::Dummy};
        else if (has_single_value(generalise<IntegerVariableID>(var)))
            return pair{Inference::NoChange, HowChanged::Dummy};
        else {
            assign_to_state_of(var) = IntegerVariableConstantState{value};
            return pair{Inference::Change, HowChanged::Instantiated};
        }

    case NotEqual:
        // If the value isn't in the domain, we don't need to do anything.
        // Otherwise...
        if (! in_domain(generalise<IntegerVariableID>(var), value))
            return pair{Inference::NoChange, HowChanged::Dummy};

        return overloaded{
            [&](IntegerVariableConstantState &) -> pair<Inference, HowChanged> {
                // Constant equal to the value, problem!
                return pair{Inference::Contradiction, HowChanged::Dummy};
            },
            [&](IntegerVariableRangeState & rvar) -> pair<Inference, HowChanged> {
                if (rvar.lower == rvar.upper) {
                    // Constant equal to the value, problem!
                    return pair{Inference::Contradiction, HowChanged::Dummy};
                }
                else if (rvar.lower == value) {
                    // Can just bump the bound
                    ++rvar.lower;
                    if (rvar.lower == rvar.upper) {
                        assign_to_state_of(var) = IntegerVariableConstantState{rvar.lower};
                        return pair{Inference::Change, HowChanged::Instantiated};
                    }
                    else
                        return pair{Inference::Change, HowChanged::BoundsChanged};
                }
                else if (rvar.upper == value) {
                    --rvar.upper;

                    if (rvar.lower == rvar.upper) {
                        assign_to_state_of(var) = IntegerVariableConstantState{rvar.lower};
                        return pair{Inference::Change, HowChanged::Instantiated};
                    }
                    else
                        return pair{Inference::Change, HowChanged::BoundsChanged};
                }
                else {
                    // Holey domain, convert to set. This should handle offsets...
                    if (rvar.lower < 0_i || rvar.upper >= Integer{Bits::number_of_bits}) {
                        auto values = make_shared<set<Integer>>();
                        for (Integer v = rvar.lower; v <= rvar.upper; ++v)
                            if (v != value)
                                values->insert(v);
                        assign_to_state_of(var) = IntegerVariableSetState{values};
                    }
                    else {
                        IntegerVariableSmallSetState svar{Integer{0}, Bits{}};
                        for (Integer v = rvar.lower; v <= rvar.upper; ++v)
                            if (v != value)
                                svar.bits.set(v.raw_value);
                        assign_to_state_of(var) = move(svar);
                    }
                    return pair{Inference::Change, HowChanged::InteriorValuesChanged};
                }
            },
            [&](IntegerVariableSmallSetState & svar) -> pair<Inference, HowChanged> {
                // Knock out the value
                bool is_bound = (value == svar.lower + Integer{svar.bits.countr_zero()}) ||
                    (value == svar.lower + Integer{Bits::number_of_bits} - Integer{svar.bits.countl_zero()} - 1_i);
                svar.bits.reset((value - svar.lower).raw_value);
                if (svar.bits.has_single_bit()) {
                    assign_to_state_of(var) = IntegerVariableConstantState{svar.lower + Integer{svar.bits.countr_zero()}};
                    return pair{Inference::Change, HowChanged::Instantiated};
                }
                else if (svar.bits.none())
                    return pair{Inference::Contradiction, HowChanged::Dummy};
                else if (is_bound)
                    return pair{Inference::Change, HowChanged::BoundsChanged};
                else
                    return pair{Inference::Change, HowChanged::InteriorValuesChanged};
            },
            [&](IntegerVariableSetState & svar) -> pair<Inference, HowChanged> {
                // Knock out the value
                bool is_bound = (value == *svar.values->begin() || value == *svar.values->rbegin());
                if (1 == svar.values->size())
                    return pair{Inference::Contradiction, HowChanged::Dummy};
                else if (2 == svar.values->size()) {
                    assign_to_state_of(var) = IntegerVariableConstantState{
                        value == *svar.values->begin() ? *next(svar.values->begin()) : *svar.values->begin()};
                    return pair{Inference::Change, HowChanged::Instantiated};
                }
                else if (svar.values.unique()) {
                    svar.values->erase(value);
                    return pair{Inference::Change, is_bound ? HowChanged::BoundsChanged : HowChanged::InteriorValuesChanged};
                }
                else {
                    auto new_values = make_shared<set<Integer>>(*svar.values);
                    new_values->erase(value);
                    svar.values = new_values;
                    return pair{Inference::Change, is_bound ? HowChanged::BoundsChanged : HowChanged::InteriorValuesChanged};
                }
            }}
            .visit(state_of(var, space));

    case Less:
        return overloaded{
            [&](IntegerVariableConstantState & c) -> pair<Inference, HowChanged> {
                // Ok if the constant is less, otherwise contradiction
                return pair{c.value < value ? Inference::NoChange : Inference::Contradiction, HowChanged::Dummy};
            },
            [&](IntegerVariableRangeState & rvar) -> pair<Inference, HowChanged> {
                if (rvar.upper >= value) {
                    rvar.upper = value - 1_i;
                    if (rvar.lower == rvar.upper) {
                        assign_to_state_of(var) = IntegerVariableConstantState{rvar.lower};
                        return pair{Inference::Change, HowChanged::Instantiated};
                    }
                    else if (rvar.lower > rvar.upper)
                        return pair{Inference::Contradiction, HowChanged::Dummy};
                    else
                        return pair{Inference::Change, HowChanged::BoundsChanged};
                }
                else
                    return pair{Inference::NoChange, HowChanged::Dummy};
            },
            [&](IntegerVariableSmallSetState & svar) -> pair<Inference, HowChanged> {
                // This should be much smarter...
                auto pc_before = svar.bits.popcount();
                for (int i = 0; i < Bits::number_of_bits; ++i)
                    if (svar.lower + Integer{i} >= value)
                        svar.bits.reset(i);
                auto pc_after = svar.bits.popcount();
                if (pc_after == 0)
                    return pair{Inference::Contradiction, HowChanged::Dummy};
                if (pc_after == 1) {
                    assign_to_state_of(var) = IntegerVariableConstantState{*optional_single_value(generalise<IntegerVariableID>(var))};
                    return pair{Inference::Change, HowChanged::Instantiated};
                }
                return pc_before == pc_after ? pair{Inference::NoChange, HowChanged::Dummy} : pair{Inference::Change, HowChanged::BoundsChanged};
            },
            [&](IntegerVariableSetState & svar) -> pair<Inference, HowChanged> {
                // This should also be much smarter...
                auto erase_from = svar.values->upper_bound(value - 1_i);
                if (erase_from == svar.values->end())
                    return pair{Inference::NoChange, HowChanged::Dummy};

                if (! svar.values.unique()) {
                    svar.values = make_shared<set<Integer>>(*svar.values);
                    erase_from = svar.values->upper_bound(value - 1_i);
                }

                svar.values->erase(erase_from, svar.values->end());
                if (svar.values->size() == 0)
                    return pair{Inference::Contradiction, HowChanged::Dummy};
                else if (svar.values->size() == 1) {
                    assign_to_state_of(var) = IntegerVariableConstantState{*optional_single_value(generalise<IntegerVariableID>(var))};
                    return pair{Inference::Change, HowChanged::Instantiated};
                }
                else
                    return pair{Inference::Change, HowChanged::BoundsChanged};
            }}
            .visit(state_of(var, space));
        break;

    case GreaterEqual:
        return overloaded{
            [&](IntegerVariableConstantState & c) -> pair<Inference, HowChanged> {
                // Ok if the constant is greater or equal, otherwise contradiction
                return pair{c.value >= value ? Inference::NoChange : Inference::Contradiction, HowChanged::Dummy};
            },
            [&](IntegerVariableRangeState & rvar) -> pair<Inference, HowChanged> {
                if (rvar.lower < value) {
                    rvar.lower = value;
                    if (rvar.lower == rvar.upper) {
                        assign_to_state_of(var) = IntegerVariableConstantState{rvar.lower};
                        return pair{Inference::Change, HowChanged::Instantiated};
                    }
                    else if (rvar.lower > rvar.upper)
                        return pair{Inference::Contradiction, HowChanged::Dummy};
                    else
                        return pair{Inference::Change, HowChanged::BoundsChanged};
                }
                return pair{Inference::NoChange, HowChanged::Dummy};
            },
            [&](IntegerVariableSmallSetState & svar) -> pair<Inference, HowChanged> {
                // This should be much smarter...
                auto pc_before = svar.bits.popcount();
                for (int i = 0; i < Bits::number_of_bits; ++i)
                    if (svar.lower + Integer{i} < value)
                        svar.bits.reset(i);
                auto pc_after = svar.bits.popcount();
                if (pc_after == 0)
                    return pair{Inference::Contradiction, HowChanged::Dummy};
                if (pc_after == 1) {
                    assign_to_state_of(var) = IntegerVariableConstantState{*optional_single_value(generalise<IntegerVariableID>(var))};
                    return pair{Inference::Change, HowChanged::Instantiated};
                }
                return pc_before == pc_after ? pair{Inference::NoChange, HowChanged::Dummy} : pair{Inference::Change, HowChanged::BoundsChanged};
            },
            [&](IntegerVariableSetState & svar) -> pair<Inference, HowChanged> {
                // This should also be much smarter...
                auto erase_to = svar.values->lower_bound(value);
                if (erase_to == svar.values->begin())
                    return pair{Inference::NoChange, HowChanged::Dummy};

                if (! svar.values.unique()) {
                    svar.values = make_shared<set<Integer>>(*svar.values);
                    erase_to = svar.values->lower_bound(value);
                }

                svar.values->erase(svar.values->begin(), erase_to);
                if (svar.values->size() == 0)
                    return pair{Inference::Contradiction, HowChanged::Dummy};
                else if (svar.values->size() == 1) {
                    assign_to_state_of(var) = IntegerVariableConstantState{*optional_single_value(generalise<IntegerVariableID>(var))};
                    return pair{Inference::Change, HowChanged::Instantiated};
                }
                else
                    return pair{Inference::Change, HowChanged::BoundsChanged};
            }}
            .visit(state_of(var, space));
        break;
    }

    throw NonExhaustiveSwitch{};
}

auto State::infer(const Literal & lit, Justification just) -> Inference
{
    return overloaded{
        [&](const LiteralFromIntegerVariable & ilit) -> Inference {
            auto [actual_var, offset] = underlying_direct_variable_and_offset(ilit.var);
            auto [inference, how_changed] = infer_literal_from_direct_integer_variable(actual_var, ilit.op, ilit.value - offset);
            switch (inference) {
            case Inference::NoChange:
                return Inference::NoChange;

            case Inference::Contradiction:
                if (_imp->problem->optional_proof())
                    _imp->problem->optional_proof()->infer(*this, FalseLiteral{}, just);
                return Inference::Contradiction;

            case Inference::Change:
                remember_change(get<SimpleIntegerVariableID>(actual_var), how_changed);
                if (_imp->problem->optional_proof())
                    _imp->problem->optional_proof()->infer(*this, lit, just);
                return Inference::Change;
            }

            throw NonExhaustiveSwitch{};
        },
        [](const TrueLiteral &) {
            return Inference::NoChange;
        },
        [&](const FalseLiteral &) {
            if (_imp->problem->optional_proof())
                _imp->problem->optional_proof()->infer(*this, FalseLiteral{}, just);
            return Inference::Contradiction;
        }}
        .visit(lit);
}

auto State::infer_all(const vector<Literal> & lits, Justification just) -> Inference
{
    Inference result = Inference::NoChange;
    for (auto & lit : lits) {
        switch (infer(lit, just)) {
        case Inference::NoChange:
            break;
        case Inference::Change:
            result = Inference::Change;
            break;
        case Inference::Contradiction:
            return Inference::Contradiction;
        }

        // only do justifications once
        if (_imp->problem->optional_proof())
            visit([&](const auto & j) -> void {
                if constexpr (is_same_v<decay_t<decltype(j)>, JustifyExplicitly>)
                    just = JustifyUsingRUP{};
            },
                just);
    }

    return result;
}

auto State::guess(const Literal & lit) -> void
{
    switch (infer(lit, Guess{})) {
    case Inference::NoChange:
    case Inference::Change:
        _imp->guesses.push_back(lit);
        return;

    case Inference::Contradiction:
        throw UnexpectedException{"couldn't infer a branch variable"};
    }
}

auto State::lower_bound(const IntegerVariableID var) const -> Integer
{
    auto [actual_var, offset] = underlying_direct_variable_and_offset(var);
    IntegerVariableState space = IntegerVariableConstantState{0_i};
    return overloaded{
               [](const IntegerVariableRangeState & v) { return v.lower; },
               [](const IntegerVariableConstantState & v) { return v.value; },
               [](const IntegerVariableSmallSetState & v) { return v.lower + Integer{v.bits.countr_zero()}; },
               [](const IntegerVariableSetState & v) { return *v.values->begin(); }}
               .visit(state_of(actual_var, space)) +
        offset;
}

auto State::upper_bound(const IntegerVariableID var) const -> Integer
{
    auto [actual_var, offset] = underlying_direct_variable_and_offset(var);
    IntegerVariableState space = IntegerVariableConstantState{0_i};
    return overloaded{
               [](const IntegerVariableRangeState & v) { return v.upper; },
               [](const IntegerVariableConstantState & v) { return v.value; },
               [](const IntegerVariableSmallSetState & v) { return v.lower + Integer{Bits::number_of_bits} - Integer{v.bits.countl_zero()} - 1_i; },
               [](const IntegerVariableSetState & v) { return *v.values->rbegin(); }}
               .visit(state_of(actual_var, space)) +
        offset;
}

auto State::bounds(const IntegerVariableID var) const -> pair<Integer, Integer>
{
    auto [actual_var, offset] = underlying_direct_variable_and_offset(var);
    IntegerVariableState space = IntegerVariableConstantState{0_i};
    auto result = overloaded{
        [](const IntegerVariableRangeState & v) { return pair{v.lower, v.upper}; },
        [](const IntegerVariableConstantState & v) { return pair{v.value, v.value}; },
        [](const IntegerVariableSmallSetState & v) { return pair{
                                                         v.lower + Integer{v.bits.countr_zero()},
                                                         v.lower + Integer{Bits::number_of_bits} - Integer{v.bits.countl_zero()} - 1_i}; },
        [](const IntegerVariableSetState & v) { return pair{*v.values->begin(), *v.values->rbegin()}; }}
                      .visit(state_of(actual_var, space));
    return pair{result.first + offset, result.second + offset};
}

auto State::in_domain(const IntegerVariableID var, const Integer val) const -> bool
{
    auto [actual_var, offset] = underlying_direct_variable_and_offset(var);
    auto actual_val = val - offset;
    IntegerVariableState space = IntegerVariableConstantState{0_i};
    return overloaded{
        [val = actual_val](const IntegerVariableRangeState & v) { return val >= v.lower && val <= v.upper; },
        [val = actual_val](const IntegerVariableConstantState & v) { return val == v.value; },
        [val = actual_val](const IntegerVariableSmallSetState & v) {
            if (val < v.lower || val > (v.lower + Integer{Bits::number_of_bits - 1}))
                return false;
            else
                return v.bits.test((val - v.lower).raw_value);
        },
        [val = actual_val](const IntegerVariableSetState & v) { return v.values->end() != v.values->find(val); }}
        .visit(state_of(actual_var, space));
}

auto State::domain_has_holes(const IntegerVariableID var) const -> bool
{
    auto [actual_var, _] = underlying_direct_variable_and_offset(var);
    IntegerVariableState space = IntegerVariableConstantState{0_i};
    return overloaded{
        [](const IntegerVariableRangeState &) { return false; },
        [](const IntegerVariableConstantState &) { return false; },
        [](const IntegerVariableSmallSetState &) { return true; },
        [](const IntegerVariableSetState &) { return true; }}
        .visit(state_of(actual_var, space));
}

auto State::optional_single_value(const IntegerVariableID var) const -> optional<Integer>
{
    auto [actual_var, offset] = underlying_direct_variable_and_offset(var);
    IntegerVariableState space = IntegerVariableConstantState{0_i};
    auto result = overloaded{
        [](const IntegerVariableRangeState & v) -> optional<Integer> {
            if (v.lower == v.upper)
                return make_optional(v.lower);
            else
                return nullopt;
        },
        [](const IntegerVariableConstantState & v) -> optional<Integer> {
            return make_optional(v.value);
        },
        [](const IntegerVariableSmallSetState & v) -> optional<Integer> {
            if (v.bits.has_single_bit())
                return make_optional(v.lower + Integer{v.bits.countr_zero()});
            else
                return nullopt;
        },
        [](const IntegerVariableSetState & v) -> optional<Integer> {
            if (1 == v.values->size())
                return make_optional(*v.values->begin());
            else
                return nullopt;
        }}.visit(state_of(actual_var, space));

    return result ? *result + offset : result;
}

auto State::has_single_value(const IntegerVariableID var) const -> bool
{
    auto [actual_var, _] = underlying_direct_variable_and_offset(var);
    IntegerVariableState space = IntegerVariableConstantState{0_i};
    return overloaded{
        [](const IntegerVariableRangeState & v) -> bool { return v.lower == v.upper; },
        [](const IntegerVariableConstantState &) -> bool { return true; },
        [](const IntegerVariableSmallSetState & v) -> bool { return v.bits.has_single_bit(); },
        [](const IntegerVariableSetState & v) -> bool { return 1 == v.values->size(); }}
        .visit(state_of(actual_var, space));
}

auto State::domain_size(const IntegerVariableID var) const -> Integer
{
    auto [actual_var, _] = underlying_direct_variable_and_offset(var);
    IntegerVariableState space = IntegerVariableConstantState{0_i};
    return overloaded{
        [](const IntegerVariableConstantState &) { return Integer{1}; },
        [](const IntegerVariableRangeState & r) { return r.upper - r.lower + Integer{1}; },
        [](const IntegerVariableSmallSetState & s) { return Integer{s.bits.popcount()}; },
        [](const IntegerVariableSetState & s) { return Integer(s.values->size()); }}
        .visit(state_of(actual_var, space));
}

auto State::for_each_value(const IntegerVariableID var, function<auto(Integer)->void> f) const -> void
{
    for_each_value_while(var, [&](Integer v) -> bool {
        f(v);
        return true;
    });
}

auto State::for_each_value_while(const IntegerVariableID var, function<auto(Integer)->bool> f) const -> void
{
    auto [actual_var, offset] = underlying_direct_variable_and_offset(var);

    IntegerVariableState space = IntegerVariableConstantState{0_i};
    const IntegerVariableState & var_ref = state_of(actual_var, space);
    IntegerVariableState var_copy = var_ref;

    overloaded{
        [&](const IntegerVariableConstantState & c) {
            f(c.value + offset);
        },
        [&](const IntegerVariableRangeState & r) {
            for (auto v = r.lower; v <= r.upper; ++v)
                if (! f(v + offset))
                    break;
        },
        [&](const IntegerVariableSmallSetState & r) {
            for (unsigned b = 0; b < Bits::number_of_bits; ++b)
                if (r.bits.test(b))
                    if (! f(r.lower + Integer{b} + offset))
                        break;
        },
        [&](const IntegerVariableSetState & s) {
            for (auto & v : *s.values)
                if (! f(v + offset))
                    break;
        }}
        .visit(var_copy);
}

auto State::operator()(const IntegerVariableID & i) const -> Integer
{
    if (auto result = optional_single_value(i))
        return *result;
    throw VariableDoesNotHaveUniqueValue{"Integer variable " + debug_string(i)};
}

auto State::new_epoch() -> Timestamp
{
    if (! _imp->changed.empty())
        throw UnimplementedException{};

    _imp->integer_variable_states.push_back(_imp->integer_variable_states.back());
    _imp->on_backtracks.emplace_back();

    return Timestamp{_imp->integer_variable_states.size() - 1, _imp->guesses.size()};
}

auto State::backtrack(Timestamp t) -> void
{
    _imp->integer_variable_states.resize(t.when);
    _imp->changed.clear();
    _imp->guesses.erase(_imp->guesses.begin() + t.how_many_guesses, _imp->guesses.end());

    while (_imp->on_backtracks.size() > t.when) {
        for (auto & f : _imp->on_backtracks.back())
            f();
        _imp->on_backtracks.pop_back();
    }
}

auto State::remember_change(const SimpleIntegerVariableID v, HowChanged h) -> void
{
    auto [it, _] = _imp->changed.emplace(v, h);

    switch (h) {
    case HowChanged::InteriorValuesChanged:
        return;

    case HowChanged::BoundsChanged:
        if (it->second == HowChanged::InteriorValuesChanged)
            it->second = HowChanged::BoundsChanged;
        return;

    case HowChanged::Instantiated:
        it->second = HowChanged::Instantiated;
        return;

    case HowChanged::Dummy:
        break;
    }

    throw NonExhaustiveSwitch{};
}

auto State::extract_changed_variables(function<auto(SimpleIntegerVariableID, HowChanged)->void> f) -> void
{
    for (auto & [c, h] : _imp->changed)
        f(c, h);
    _imp->changed.clear();
}

auto State::for_each_guess(function<auto(Literal)->void> f) const -> void
{
    for (auto & g : _imp->guesses)
        f(g);
}

auto State::add_proof_steps(JustifyExplicitly why) -> void
{
    if (_imp->problem->optional_proof()) {
        vector<ProofLine> to_delete;
        _imp->problem->optional_proof()->add_proof_steps(why, to_delete);
        _imp->problem->optional_proof()->delete_proof_lines(to_delete);
    }
}

auto State::want_proofs() const -> bool
{
    return _imp->problem->optional_proof() != nullopt;
}

auto State::literal_is_nonfalsified(const Literal & lit) const -> bool
{
    return overloaded{
        [&](const LiteralFromIntegerVariable & ilit) -> bool {
            switch (ilit.op) {
                using enum LiteralFromIntegerVariable::Operator;
            case Equal:
                return in_domain(ilit.var, ilit.value);
            case Less:
                return lower_bound(ilit.var) < ilit.value;
            case GreaterEqual:
                return upper_bound(ilit.var) >= ilit.value;
            case NotEqual: {
                auto single_value = optional_single_value(ilit.var);
                return (nullopt == single_value || *single_value != ilit.value);
            }
            }

            throw NonExhaustiveSwitch{};
        },
        [](const TrueLiteral &) { return true; },
        [](const FalseLiteral &) { return false; }}
        .visit(lit);
}

auto State::test_literal(const Literal & lit) const -> LiteralIs
{
    return overloaded{
        [&](const LiteralFromIntegerVariable & ilit) -> LiteralIs {
            switch (ilit.op) {
                using enum LiteralFromIntegerVariable::Operator;
            case Equal:
                if (! in_domain(ilit.var, ilit.value))
                    return LiteralIs::DefinitelyFalse;
                else if (has_single_value(ilit.var))
                    return LiteralIs::DefinitelyTrue;
                else
                    return LiteralIs::Undecided;

            case Less:
                if (lower_bound(ilit.var) < ilit.value) {
                    if (upper_bound(ilit.var) < ilit.value)
                        return LiteralIs::DefinitelyTrue;
                    else
                        return LiteralIs::Undecided;
                }
                else
                    return LiteralIs::DefinitelyFalse;

            case GreaterEqual:
                if (upper_bound(ilit.var) >= ilit.value) {
                    if (lower_bound(ilit.var) >= ilit.value)
                        return LiteralIs::DefinitelyTrue;
                    else
                        return LiteralIs::Undecided;
                }
                else
                    return LiteralIs::DefinitelyFalse;

            case NotEqual:
                if (! in_domain(ilit.var, ilit.value))
                    return LiteralIs::DefinitelyTrue;
                else if (has_single_value(ilit.var))
                    return LiteralIs::DefinitelyFalse;
                else
                    return LiteralIs::Undecided;
            }

            throw NonExhaustiveSwitch{};
        },
        [](const TrueLiteral &) { return LiteralIs::DefinitelyTrue; },
        [](const FalseLiteral &) { return LiteralIs::DefinitelyFalse; }}
        .visit(lit);
}

auto State::on_backtrack(std::function<auto()->void> f) -> void
{
    _imp->on_backtracks.back().push_back(move(f));
}
