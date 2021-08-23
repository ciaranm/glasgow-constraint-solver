/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/state.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>

#include "util/overloaded.hh"

#include <algorithm>
#include <list>
#include <string>
#include <type_traits>
#include <vector>

using namespace gcs;

using std::decay_t;
using std::find;
using std::function;
using std::get_if;
using std::is_same_v;
using std::list;
using std::make_optional;
using std::make_shared;
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

struct State::Imp
{
    const Problem * const problem;

    list<vector<IntegerVariable> > integer_variables;
    set<VariableID> changed;
    list<Literal> guesses;

    Imp(const Problem * const p) :
        problem(p)
    {
    }
};

State::State(const Problem * const problem) :
    _imp(new Imp{ problem })
{
    _imp->integer_variables.emplace_back();
}

State::State(State && other) noexcept = default;

State::~State() = default;

auto State::clone() const -> State
{
    State result(_imp->problem);
    result._imp->integer_variables = _imp->integer_variables;
    result._imp->changed = _imp->changed;
    return result;
}

auto State::create_integer_variable(Integer lower, Integer upper) -> IntegerVariableID
{
    if (lower == upper)
        _imp->integer_variables.back().push_back(IntegerConstant{ lower });
    else
        _imp->integer_variables.back().push_back(IntegerRangeVariable{ lower, upper });

    auto result = IntegerVariableID{ _imp->integer_variables.back().size() - 1 };
    remember_change(result);
    return result;
}

auto State::non_constant_integer_variable(const IntegerVariableID i) -> IntegerVariable &
{
    return visit(overloaded {
            [&] (const unsigned long long index) -> IntegerVariable & { return _imp->integer_variables.back()[index]; },
            [&] (const Integer)                  -> IntegerVariable & { throw UnexpectedException{ "unexpected constant" }; }
            }, i.index_or_const_value);
}

auto State::integer_variable(const IntegerVariableID i, IntegerVariable & space) -> IntegerVariable &
{
    return visit(overloaded {
            [&] (const unsigned long long index) -> IntegerVariable & { return _imp->integer_variables.back()[index]; },
            [&] (const Integer x)                -> IntegerVariable & { space = IntegerConstant{ x }; return space; }
            }, i.index_or_const_value);
}

auto State::integer_variable(const IntegerVariableID i, IntegerVariable & space) const -> const IntegerVariable &
{
    return visit(overloaded {
            [&] (const unsigned long long index) -> IntegerVariable & { return _imp->integer_variables.back()[index]; },
            [&] (const Integer x)                -> IntegerVariable & { space = IntegerConstant{ x }; return space; }
            }, i.index_or_const_value);
}

auto State::infer_boolean(const LiteralFromBooleanVariable & blit) -> Inference
{
    return visit(overloaded {
            [&] (const unsigned long long) -> Inference {
                throw UnimplementedException{ };
            },
            [&] (bool x) -> Inference {
                return (x == (blit.state == LiteralFromBooleanVariable::True)) ? Inference::NoChange : Inference::Contradiction;
            }
        }, blit.var.index_or_const_value);
}

auto State::infer_integer(const LiteralFromIntegerVariable & ilit) -> Inference
{
    IntegerVariable space = IntegerConstant{ 0_i };

    switch (ilit.state) {
        case LiteralFromIntegerVariable::Equal:
            // Has to be equal. If the value isn't in the domain, we've found a
            // contradiction, otherwise update to a constant value.
            if (! in_domain(ilit.var, ilit.value))
                return Inference::Contradiction;
            else if (optional_single_value(ilit.var))
                return Inference::NoChange;
            else {
                non_constant_integer_variable(ilit.var) = IntegerConstant{ ilit.value };
                return Inference::Change;
            }

        case LiteralFromIntegerVariable::NotEqual:
            // If the value isn't in the domain, we don't need to do anything.
            // Otherwise...
            if (! in_domain(ilit.var, ilit.value))
                return Inference::NoChange;

            return visit(overloaded {
                    [&] (IntegerConstant &) -> Inference {
                        // Constant equal to the value, problem!
                        return Inference::Contradiction;
                    },
                    [&] (IntegerRangeVariable & rvar) -> Inference {
                        if (rvar.lower == rvar.upper) {
                            // Constant equal to the value, problem!
                            return Inference::Contradiction;
                        }
                        else if (rvar.lower == ilit.value) {
                            // Can just bump the bound
                            ++rvar.lower;
                            if (rvar.lower == rvar.upper)
                                non_constant_integer_variable(ilit.var) = IntegerConstant{ rvar.lower };
                            return Inference::Change;
                        }
                        else if (rvar.upper == ilit.value) {
                            --rvar.upper;

                            if (rvar.lower == rvar.upper)
                                non_constant_integer_variable(ilit.var) = IntegerConstant{ rvar.lower };
                            return Inference::Change;
                        }
                        else {
                            // Holey domain, convert to set. This should handle offsets...
                            if (rvar.lower < 0_i || rvar.upper >= Integer{ Bits::number_of_bits }) {
                                auto values = make_shared<set<Integer> >();
                                for (Integer v = rvar.lower ; v <= rvar.upper ; ++v)
                                    if (v != ilit.value)
                                        values->insert(v);
                                non_constant_integer_variable(ilit.var) = IntegerSetVariable{ values };
                            }
                            else {
                                IntegerSmallSetVariable svar{ Integer{ 0 }, Bits{ 0 } };
                                for (Integer v = rvar.lower ; v <= rvar.upper ; ++v)
                                    if (v != ilit.value)
                                        svar.bits.set(v.raw_value);
                                non_constant_integer_variable(ilit.var) = move(svar);
                            }
                            return Inference::Change;
                        }
                    },
                    [&] (IntegerSmallSetVariable & svar) -> Inference {
                        // Knock out the value
                        svar.bits.reset(ilit.value.raw_value);
                        if (svar.bits.has_single_bit())
                            non_constant_integer_variable(ilit.var) = IntegerConstant{ svar.lower + Integer{ svar.bits.countr_zero() } };
                        else if (svar.bits.none())
                            return Inference::Contradiction;
                        return Inference::Change;
                    },
                    [&] (IntegerSetVariable & svar) -> Inference {
                        // Knock out the value
                        if (1 == svar.values->size())
                            return Inference::Contradiction;
                        else if (2 == svar.values->size()) {
                            non_constant_integer_variable(ilit.var) = IntegerConstant{ ilit.value == *svar.values->begin() ? *next(svar.values->begin()) : *svar.values->begin() };
                            return Inference::Change;
                        }
                        else if (svar.values.unique()) {
                            svar.values->erase(ilit.value);
                            return Inference::Change;
                        }
                        else {
                            auto new_values = make_shared<set<Integer> >(*svar.values);
                            new_values->erase(ilit.value);
                            svar.values = new_values;
                            return Inference::Change;
                        }
                    }
                }, integer_variable(ilit.var, space));

        case LiteralFromIntegerVariable::Less:
            return visit(overloaded {
                    [&] (IntegerConstant & c) -> Inference {
                        // Ok if the constant is less, otherwise contradiction
                        return c.value < ilit.value ? Inference::NoChange : Inference::Contradiction;
                    },
                    [&] (IntegerRangeVariable & rvar) -> Inference {
                        bool changed = false;
                        if (rvar.upper >= ilit.value) {
                            changed = true;
                            rvar.upper = ilit.value - 1_i;
                        }
                        if (rvar.lower == rvar.upper)
                            non_constant_integer_variable(ilit.var) = IntegerConstant{ rvar.lower };
                        else if (rvar.lower > rvar.upper)
                            return Inference::Contradiction;
                        return changed ? Inference::Change : Inference::NoChange;
                    },
                    [&] (IntegerSmallSetVariable & svar) -> Inference {
                        // This should be much smarter...
                        auto pc_before = svar.bits.popcount();
                        for (int i = 0 ; i < Bits::number_of_bits ; ++i)
                            if (svar.lower + Integer{ i } >= ilit.value)
                                svar.bits.reset(i);
                        auto pc_after = svar.bits.popcount();
                        if (pc_after == 0)
                            return Inference::Contradiction;
                        if (pc_after == 1)
                            non_constant_integer_variable(ilit.var) = IntegerConstant{ *optional_single_value(ilit.var) };
                        return pc_before == pc_after ? Inference::NoChange : Inference::Change;
                    },
                    [&] (IntegerSetVariable & svar) -> Inference {
                        // This should also be much smarter...
                        auto erase_from = svar.values->upper_bound(ilit.value);
                        if (erase_from == svar.values->end())
                            return Inference::NoChange;

                         if (! svar.values.unique()) {
                             svar.values = make_shared<set<Integer> >(*svar.values);
                             erase_from = svar.values->upper_bound(ilit.value);
                         }

                         svar.values->erase(erase_from, svar.values->end());
                         if (svar.values->size() == 0)
                             return Inference::Contradiction;
                         else if (svar.values->size() == 1)
                             non_constant_integer_variable(ilit.var) = IntegerConstant{ *optional_single_value(ilit.var) };
                         return Inference::Change;
                    }
                }, integer_variable(ilit.var, space));
            break;

        case LiteralFromIntegerVariable::GreaterEqual:
            return visit(overloaded {
                    [&] (IntegerConstant & c) -> Inference {
                        // Ok if the constant is greater or equal, otherwise contradiction
                        return c.value >= ilit.value ? Inference::NoChange : Inference::Contradiction;
                    },
                    [&] (IntegerRangeVariable & rvar) -> Inference {
                        bool changed = false;
                        if (rvar.lower < ilit.value) {
                            changed = true;
                            rvar.lower = ilit.value;
                        }
                        if (rvar.lower == rvar.upper)
                            non_constant_integer_variable(ilit.var) = IntegerConstant{ rvar.lower };
                        else if (rvar.lower > rvar.upper)
                            return Inference::Contradiction;
                        return changed ? Inference::Change : Inference::NoChange;
                    },
                    [&] (IntegerSmallSetVariable & svar) -> Inference {
                        // This should be much smarter...
                        auto pc_before = svar.bits.popcount();
                        for (int i = 0 ; i < Bits::number_of_bits ; ++i)
                            if (svar.lower + Integer{ i } < ilit.value)
                                svar.bits.reset(i);
                        auto pc_after = svar.bits.popcount();
                        if (pc_after == 0)
                            return Inference::Contradiction;
                        if (pc_after == 1)
                            non_constant_integer_variable(ilit.var) = IntegerConstant{ *optional_single_value(ilit.var) };
                        return pc_before == pc_after ? Inference::NoChange : Inference::Change;
                    },
                    [&] (IntegerSetVariable & svar) -> Inference {
                        // This should also be much smarter...
                        auto erase_to = svar.values->lower_bound(ilit.value);
                        if (erase_to == svar.values->begin())
                            return Inference::NoChange;

                         if (! svar.values.unique()) {
                             svar.values = make_shared<set<Integer> >(*svar.values);
                             erase_to = svar.values->lower_bound(ilit.value);
                         }

                         svar.values->erase(svar.values->begin(), erase_to);
                         if (svar.values->size() == 0)
                             return Inference::Contradiction;
                         else if (svar.values->size() == 1)
                             non_constant_integer_variable(ilit.var) = IntegerConstant{ *optional_single_value(ilit.var) };
                         return Inference::Change;
                    }
                }, integer_variable(ilit.var, space));
            break;
    }

    throw NonExhaustiveSwitch{ };
}

auto State::infer(const Literal & lit, Justification just) -> Inference
{
    auto [ inference, var ] = visit(overloaded {
            [&] (const LiteralFromBooleanVariable & blit) -> pair<Inference, VariableID> {
                return pair{ infer_boolean(blit), blit.var };
            },
            [&] (const LiteralFromIntegerVariable & ilit) -> pair<Inference, VariableID> {
                return pair{ infer_integer(ilit), ilit.var };
            }
            }, lit);

    switch (inference) {
        case Inference::NoChange:
            break;
        case Inference::Contradiction:
            if (_imp->problem->optional_proof())
                _imp->problem->optional_proof()->infer(*this, lit, just);
            break;
        case Inference::Change:
            remember_change(var);
            if (_imp->problem->optional_proof())
                _imp->problem->optional_proof()->infer(*this, lit, just);
            break;
    }

    return inference;
}

auto State::infer_all(const std::vector<Literal> & lits, Justification just) -> Inference
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
            visit([&] (const auto & j) -> void {
                    if constexpr (is_same_v<decay_t<decltype(j)>, JustifyExplicitly>)
                        just = JustifyUsingRUP{ };
                }, just);
    }

    return result;
}

auto State::guess(const Literal & lit) -> void
{
    switch (infer(lit, Guess{ })) {
        case Inference::NoChange:
        case Inference::Change:
            _imp->guesses.push_back(lit);
            return;

        case Inference::Contradiction:
            throw UnexpectedException{ "couldn't infer a branch variable" };
    }
}

auto State::lower_bound(const IntegerVariableID var) const -> Integer
{
    IntegerVariable space = IntegerConstant{ 0_i };
    return visit(overloaded {
            [] (const IntegerRangeVariable & v) { return v.lower; },
            [] (const IntegerConstant & v) { return v.value; },
            [] (const IntegerSmallSetVariable & v) { return v.lower + Integer{ v.bits.countr_zero() }; },
            [] (const IntegerSetVariable & v) { return *v.values->begin(); }
            }, integer_variable(var, space));
}

auto State::upper_bound(const IntegerVariableID var) const -> Integer
{
    IntegerVariable space = IntegerConstant{ 0_i };
    return visit(overloaded {
            [] (const IntegerRangeVariable & v) { return v.upper; },
            [] (const IntegerConstant & v) { return v.value; },
            [] (const IntegerSmallSetVariable & v) { return v.lower + Integer{ Bits::number_of_bits } - Integer{ v.bits.countl_zero() }; },
            [] (const IntegerSetVariable & v) { return *v.values->rbegin(); }
            }, integer_variable(var, space));
}

auto State::in_domain(const IntegerVariableID var, const Integer val) const -> bool
{
    IntegerVariable space = IntegerConstant{ 0_i };
    return visit(overloaded {
            [val] (const IntegerRangeVariable & v) { return val >= v.lower && val <= v.upper; },
            [val] (const IntegerConstant & v) { return val == v.value; },
            [val] (const IntegerSmallSetVariable & v) {
                if (val < v.lower || val > (v.lower + Integer{ Bits::number_of_bits - 1 }))
                    return false;
                else
                    return v.bits.test((val - v.lower).raw_value);
            },
            [val] (const IntegerSetVariable & v) { return v.values->end() != v.values->find(val); }
            }, integer_variable(var, space));
}

auto State::optional_single_value(const IntegerVariableID var) const -> optional<Integer>
{
    IntegerVariable space = IntegerConstant{ 0_i };
    return visit(overloaded {
            [] (const IntegerRangeVariable & v) -> optional<Integer> {
                if (v.lower == v.upper)
                    return make_optional(v.lower);
                else
                    return nullopt;
            },
            [] (const IntegerConstant & v) -> optional<Integer> {
                return make_optional(v.value);
            },
            [] (const IntegerSmallSetVariable & v) -> optional<Integer> {
                if (v.bits.has_single_bit())
                    return make_optional(v.lower + Integer{ v.bits.countr_zero() });
                else
                    return nullopt;
            },
            [] (const IntegerSetVariable & v) -> optional<Integer> {
                if (1 == v.values->size())
                    return make_optional(*v.values->begin());
                else
                    return nullopt;
            } }, integer_variable(var, space));
}

auto State::domain_size(const IntegerVariableID var) const -> Integer
{
    IntegerVariable space = IntegerConstant{ 0_i };
    return visit(overloaded {
            [] (const IntegerConstant &)           { return Integer{ 1 }; },
            [] (const IntegerRangeVariable & r)    { return r.upper - r.lower + Integer{ 1 }; },
            [] (const IntegerSmallSetVariable & s) { return Integer{ s.bits.popcount() }; },
            [] (const IntegerSetVariable & s)      { return Integer(s.values->size()); }
            }, integer_variable(var, space));
}

auto State::for_each_value(const IntegerVariableID var, std::function<auto (Integer) -> void> f) const -> void
{
    for (Integer v = lower_bound(var) ; v <= upper_bound(var) ; ++v)
        if (in_domain(var, v))
            f(v);
}

auto State::optional_single_value(const BooleanVariableID v) const -> optional<bool>
{
    return visit(overloaded {
            [] (bool x) { return make_optional(x); },
            [] (unsigned long long) -> optional<bool> { throw UnimplementedException{ }; }
            }, v.index_or_const_value);
}

auto State::operator() (const IntegerVariableID & i) const -> Integer
{
    if (auto result = optional_single_value(i))
        return *result;
    throw VariableDoesNotHaveUniqueValue{ "Integer variable " + debug_string(i) };
}

auto State::new_epoch() -> Timestamp
{
    if (! _imp->changed.empty())
        throw UnimplementedException{ };

    _imp->integer_variables.push_back(_imp->integer_variables.back());
    return Timestamp{ _imp->integer_variables.size() - 1 };
}

auto State::backtrack(Timestamp t) -> void
{
    _imp->integer_variables.resize(t.when);
    _imp->changed.clear();
    _imp->guesses.pop_back();
}

auto State::remember_change(const VariableID v) -> void
{
    _imp->changed.insert(v);
}

auto State::extract_changed_variables(function<auto (VariableID) -> void> f) -> void
{
    for (auto & c : _imp->changed)
        f(c);
    _imp->changed.clear();
}

auto State::for_each_guess(std::function<auto (Literal) -> void> f) const -> void
{
    for (auto & g : _imp->guesses)
        f(g);
}

