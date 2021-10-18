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

auto gcs::increase_inference_to(Inference & current, const Inference updated) -> void
{
    switch (updated) {
        case Inference::NoChange:      break;
        case Inference::Change:        if (current != Inference::Contradiction) current = updated; break;
        case Inference::Contradiction: current = updated; break;
    }
}

struct State::Imp
{
    const Problem * const problem;

    list<vector<IntegerVariableState> > integer_variable_states;
    set<VariableID> changed;
    vector<Literal> guesses;

    Imp(const Problem * const p) :
        problem(p)
    {
    }
};

State::State(const Problem * const problem) :
    _imp(new Imp{ problem })
{
    _imp->integer_variable_states.emplace_back();
}

State::State(State && other) noexcept = default;

State::~State() = default;

auto State::clone() const -> State
{
    State result(_imp->problem);
    result._imp->integer_variable_states = _imp->integer_variable_states;
    result._imp->changed = _imp->changed;
    return result;
}

auto State::create_integer_variable(Integer lower, Integer upper) -> IntegerVariableID
{
    if (lower == upper)
        _imp->integer_variable_states.back().push_back(IntegerVariableConstantState{ lower });
    else
        _imp->integer_variable_states.back().push_back(IntegerVariableRangeState{ lower, upper });

    return IntegerVariableID{ _imp->integer_variable_states.back().size() - 1 };
}

auto State::create_pseudovariable(Integer lower, Integer upper, const optional<string> & name) -> IntegerVariableID
{
    auto result = create_integer_variable(lower, upper);
    if (_imp->problem->optional_proof())
        _imp->problem->optional_proof()->create_pseudovariable(result, lower, upper, name);
    return result;
}

auto State::non_constant_state_of(const IntegerVariableID i) -> IntegerVariableState &
{
    return visit(overloaded {
            [&] (const unsigned long long index) -> IntegerVariableState & { return _imp->integer_variable_states.back()[index]; },
            [&] (const Integer)                  -> IntegerVariableState & { throw UnexpectedException{ "unexpected constant" }; }
            }, i.index_or_const_value);
}

auto State::state_of(const IntegerVariableID i, IntegerVariableState & space) -> IntegerVariableState &
{
    return visit(overloaded {
            [&] (const unsigned long long index) -> IntegerVariableState & { return _imp->integer_variable_states.back()[index]; },
            [&] (const Integer x)                -> IntegerVariableState & { space = IntegerVariableConstantState{ x }; return space; }
            }, i.index_or_const_value);
}

auto State::state_of(const IntegerVariableID i, IntegerVariableState & space) const -> const IntegerVariableState &
{
    return visit(overloaded {
            [&] (const unsigned long long index) -> IntegerVariableState & { return _imp->integer_variable_states.back()[index]; },
            [&] (const Integer x)                -> IntegerVariableState & { space = IntegerVariableConstantState{ x }; return space; }
            }, i.index_or_const_value);
}

auto State::infer_integer(const LiteralFromIntegerVariable & ilit) -> Inference
{
    IntegerVariableState space = IntegerVariableConstantState{ 0_i };

    switch (ilit.state) {
        case LiteralFromIntegerVariable::Equal:
            // Has to be equal. If the value isn't in the domain, we've found a
            // contradiction, otherwise update to a constant value.
            if (! in_domain(ilit.var, ilit.value))
                return Inference::Contradiction;
            else if (optional_single_value(ilit.var))
                return Inference::NoChange;
            else {
                non_constant_state_of(ilit.var) = IntegerVariableConstantState{ ilit.value };
                return Inference::Change;
            }

        case LiteralFromIntegerVariable::NotEqual:
            // If the value isn't in the domain, we don't need to do anything.
            // Otherwise...
            if (! in_domain(ilit.var, ilit.value))
                return Inference::NoChange;

            return visit(overloaded {
                    [&] (IntegerVariableConstantState &) -> Inference {
                        // Constant equal to the value, problem!
                        return Inference::Contradiction;
                    },
                    [&] (IntegerVariableRangeState & rvar) -> Inference {
                        if (rvar.lower == rvar.upper) {
                            // Constant equal to the value, problem!
                            return Inference::Contradiction;
                        }
                        else if (rvar.lower == ilit.value) {
                            // Can just bump the bound
                            ++rvar.lower;
                            if (rvar.lower == rvar.upper)
                                non_constant_state_of(ilit.var) = IntegerVariableConstantState{ rvar.lower };
                            return Inference::Change;
                        }
                        else if (rvar.upper == ilit.value) {
                            --rvar.upper;

                            if (rvar.lower == rvar.upper)
                                non_constant_state_of(ilit.var) = IntegerVariableConstantState{ rvar.lower };
                            return Inference::Change;
                        }
                        else {
                            // Holey domain, convert to set. This should handle offsets...
                            if (rvar.lower < 0_i || rvar.upper >= Integer{ Bits::number_of_bits }) {
                                auto values = make_shared<set<Integer> >();
                                for (Integer v = rvar.lower ; v <= rvar.upper ; ++v)
                                    if (v != ilit.value)
                                        values->insert(v);
                                non_constant_state_of(ilit.var) = IntegerVariableSetState{ values };
                            }
                            else {
                                IntegerVariableSmallSetState svar{ Integer{ 0 }, Bits{ 0 } };
                                for (Integer v = rvar.lower ; v <= rvar.upper ; ++v)
                                    if (v != ilit.value)
                                        svar.bits.set(v.raw_value);
                                non_constant_state_of(ilit.var) = move(svar);
                            }
                            return Inference::Change;
                        }
                    },
                    [&] (IntegerVariableSmallSetState & svar) -> Inference {
                        // Knock out the value
                        svar.bits.reset((ilit.value - svar.lower).raw_value);
                        if (svar.bits.has_single_bit())
                            non_constant_state_of(ilit.var) = IntegerVariableConstantState{ svar.lower + Integer{ svar.bits.countr_zero() } };
                        else if (svar.bits.none())
                            return Inference::Contradiction;
                        return Inference::Change;
                    },
                    [&] (IntegerVariableSetState & svar) -> Inference {
                        // Knock out the value
                        if (1 == svar.values->size())
                            return Inference::Contradiction;
                        else if (2 == svar.values->size()) {
                            non_constant_state_of(ilit.var) = IntegerVariableConstantState{ ilit.value == *svar.values->begin() ? *next(svar.values->begin()) : *svar.values->begin() };
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
                }, state_of(ilit.var, space));

        case LiteralFromIntegerVariable::Less:
            return visit(overloaded {
                    [&] (IntegerVariableConstantState & c) -> Inference {
                        // Ok if the constant is less, otherwise contradiction
                        return c.value < ilit.value ? Inference::NoChange : Inference::Contradiction;
                    },
                    [&] (IntegerVariableRangeState & rvar) -> Inference {
                        bool changed = false;
                        if (rvar.upper >= ilit.value) {
                            changed = true;
                            rvar.upper = ilit.value - 1_i;
                        }
                        if (rvar.lower == rvar.upper)
                            non_constant_state_of(ilit.var) = IntegerVariableConstantState{ rvar.lower };
                        else if (rvar.lower > rvar.upper)
                            return Inference::Contradiction;
                        return changed ? Inference::Change : Inference::NoChange;
                    },
                    [&] (IntegerVariableSmallSetState & svar) -> Inference {
                        // This should be much smarter...
                        auto pc_before = svar.bits.popcount();
                        for (int i = 0 ; i < Bits::number_of_bits ; ++i)
                            if (svar.lower + Integer{ i } >= ilit.value)
                                svar.bits.reset(i);
                        auto pc_after = svar.bits.popcount();
                        if (pc_after == 0)
                            return Inference::Contradiction;
                        if (pc_after == 1)
                            non_constant_state_of(ilit.var) = IntegerVariableConstantState{ *optional_single_value(ilit.var) };
                        return pc_before == pc_after ? Inference::NoChange : Inference::Change;
                    },
                    [&] (IntegerVariableSetState & svar) -> Inference {
                        // This should also be much smarter...
                        auto erase_from = svar.values->upper_bound(ilit.value - 1_i);
                        if (erase_from == svar.values->end())
                            return Inference::NoChange;

                         if (! svar.values.unique()) {
                             svar.values = make_shared<set<Integer> >(*svar.values);
                             erase_from = svar.values->upper_bound(ilit.value - 1_i);
                         }

                         svar.values->erase(erase_from, svar.values->end());
                         if (svar.values->size() == 0)
                             return Inference::Contradiction;
                         else if (svar.values->size() == 1)
                             non_constant_state_of(ilit.var) = IntegerVariableConstantState{ *optional_single_value(ilit.var) };
                         return Inference::Change;
                    }
                }, state_of(ilit.var, space));
            break;

        case LiteralFromIntegerVariable::GreaterEqual:
            return visit(overloaded {
                    [&] (IntegerVariableConstantState & c) -> Inference {
                        // Ok if the constant is greater or equal, otherwise contradiction
                        return c.value >= ilit.value ? Inference::NoChange : Inference::Contradiction;
                    },
                    [&] (IntegerVariableRangeState & rvar) -> Inference {
                        bool changed = false;
                        if (rvar.lower < ilit.value) {
                            changed = true;
                            rvar.lower = ilit.value;
                        }
                        if (rvar.lower == rvar.upper)
                            non_constant_state_of(ilit.var) = IntegerVariableConstantState{ rvar.lower };
                        else if (rvar.lower > rvar.upper)
                            return Inference::Contradiction;
                        return changed ? Inference::Change : Inference::NoChange;
                    },
                    [&] (IntegerVariableSmallSetState & svar) -> Inference {
                        // This should be much smarter...
                        auto pc_before = svar.bits.popcount();
                        for (int i = 0 ; i < Bits::number_of_bits ; ++i)
                            if (svar.lower + Integer{ i } < ilit.value)
                                svar.bits.reset(i);
                        auto pc_after = svar.bits.popcount();
                        if (pc_after == 0)
                            return Inference::Contradiction;
                        if (pc_after == 1)
                            non_constant_state_of(ilit.var) = IntegerVariableConstantState{ *optional_single_value(ilit.var) };
                        return pc_before == pc_after ? Inference::NoChange : Inference::Change;
                    },
                    [&] (IntegerVariableSetState & svar) -> Inference {
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
                             non_constant_state_of(ilit.var) = IntegerVariableConstantState{ *optional_single_value(ilit.var) };
                         return Inference::Change;
                    }
                }, state_of(ilit.var, space));
            break;
    }

    throw NonExhaustiveSwitch{ };
}

auto State::infer(const Literal & lit, Justification just) -> Inference
{
    return visit(overloaded {
            [&] (const LiteralFromIntegerVariable & ilit) -> Inference {
                switch (infer_integer(ilit)) {
                    case Inference::NoChange:
                        return Inference::NoChange;

                    case Inference::Contradiction:
                        if (_imp->problem->optional_proof())
                            _imp->problem->optional_proof()->infer(*this, FalseLiteral{ }, just);
                        return Inference::Contradiction;

                    case Inference::Change:
                        remember_change(ilit.var);
                        if (_imp->problem->optional_proof())
                            _imp->problem->optional_proof()->infer(*this, lit, just);
                        return Inference::Change;
                }

                throw NonExhaustiveSwitch{ };
            },
            [] (const TrueLiteral &) {
                return Inference::NoChange;
            },
            [&] (const FalseLiteral &) {
                if (_imp->problem->optional_proof())
                    _imp->problem->optional_proof()->infer(*this, FalseLiteral{ }, just);
                return Inference::Contradiction;
            }
            }, lit);
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
    IntegerVariableState space = IntegerVariableConstantState{ 0_i };
    return visit(overloaded {
            [] (const IntegerVariableRangeState & v) { return v.lower; },
            [] (const IntegerVariableConstantState & v) { return v.value; },
            [] (const IntegerVariableSmallSetState & v) { return v.lower + Integer{ v.bits.countr_zero() }; },
            [] (const IntegerVariableSetState & v) { return *v.values->begin(); }
            }, state_of(var, space));
}

auto State::upper_bound(const IntegerVariableID var) const -> Integer
{
    IntegerVariableState space = IntegerVariableConstantState{ 0_i };
    return visit(overloaded {
            [] (const IntegerVariableRangeState & v) { return v.upper; },
            [] (const IntegerVariableConstantState & v) { return v.value; },
            [] (const IntegerVariableSmallSetState & v) { return v.lower + Integer{ Bits::number_of_bits } - Integer{ v.bits.countl_zero() } - 1_i; },
            [] (const IntegerVariableSetState & v) { return *v.values->rbegin(); }
            }, state_of(var, space));
}

auto State::in_domain(const IntegerVariableID var, const Integer val) const -> bool
{
    IntegerVariableState space = IntegerVariableConstantState{ 0_i };
    return visit(overloaded {
            [val] (const IntegerVariableRangeState & v) { return val >= v.lower && val <= v.upper; },
            [val] (const IntegerVariableConstantState & v) { return val == v.value; },
            [val] (const IntegerVariableSmallSetState & v) {
                if (val < v.lower || val > (v.lower + Integer{ Bits::number_of_bits - 1 }))
                    return false;
                else
                    return v.bits.test((val - v.lower).raw_value);
            },
            [val] (const IntegerVariableSetState & v) { return v.values->end() != v.values->find(val); }
            }, state_of(var, space));
}

auto State::domain_has_holes(const IntegerVariableID var) const -> bool
{
    IntegerVariableState space = IntegerVariableConstantState{ 0_i };
    return visit(overloaded {
            [] (const IntegerVariableRangeState &) { return false; },
            [] (const IntegerVariableConstantState &) { return false; },
            [] (const IntegerVariableSmallSetState &) { return true; },
            [] (const IntegerVariableSetState &) { return true; }
            }, state_of(var, space));
}

auto State::optional_single_value(const IntegerVariableID var) const -> optional<Integer>
{
    IntegerVariableState space = IntegerVariableConstantState{ 0_i };
    return visit(overloaded {
            [] (const IntegerVariableRangeState & v) -> optional<Integer> {
                if (v.lower == v.upper)
                    return make_optional(v.lower);
                else
                    return nullopt;
            },
            [] (const IntegerVariableConstantState & v) -> optional<Integer> {
                return make_optional(v.value);
            },
            [] (const IntegerVariableSmallSetState & v) -> optional<Integer> {
                if (v.bits.has_single_bit())
                    return make_optional(v.lower + Integer{ v.bits.countr_zero() });
                else
                    return nullopt;
            },
            [] (const IntegerVariableSetState & v) -> optional<Integer> {
                if (1 == v.values->size())
                    return make_optional(*v.values->begin());
                else
                    return nullopt;
            } }, state_of(var, space));
}

auto State::domain_size(const IntegerVariableID var) const -> Integer
{
    IntegerVariableState space = IntegerVariableConstantState{ 0_i };
    return visit(overloaded {
            [] (const IntegerVariableConstantState &)   { return Integer{ 1 }; },
            [] (const IntegerVariableRangeState & r)    { return r.upper - r.lower + Integer{ 1 }; },
            [] (const IntegerVariableSmallSetState & s) { return Integer{ s.bits.popcount() }; },
            [] (const IntegerVariableSetState & s)      { return Integer(s.values->size()); }
            }, state_of(var, space));
}

auto State::for_each_value(const IntegerVariableID var, function<auto (Integer) -> void> f) const -> void
{
    for_each_value_while(var, [&] (Integer v) -> bool {
            f(v);
            return true;
            });
}

auto State::for_each_value_while(const IntegerVariableID var, function<auto (Integer) -> bool> f) const -> void
{
    IntegerVariableState space = IntegerVariableConstantState{ 0_i };
    const IntegerVariableState & var_ref = state_of(var, space);
    IntegerVariableState var_copy = var_ref;

    visit(overloaded{
            [&] (const IntegerVariableConstantState & c) {
                f(c.value);
            },
            [&] (const IntegerVariableRangeState & r) {
                for (auto v = r.lower ; v <= r.upper ; ++v)
                    if (! f(v))
                        break;
            },
            [&] (const IntegerVariableSmallSetState & r) {
                for (unsigned b = 0 ; b < Bits::number_of_bits ; ++b)
                    if (r.bits.test(b))
                        if (! f(r.lower + Integer{ b }))
                            break;
            },
            [&] (const IntegerVariableSetState & s) {
                for (auto & v : *s.values)
                    if (! f(v))
                        break;
            }
            }, var_copy);
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

    _imp->integer_variable_states.push_back(_imp->integer_variable_states.back());
    return Timestamp{ _imp->integer_variable_states.size() - 1, _imp->guesses.size() };
}

auto State::backtrack(Timestamp t) -> void
{
    _imp->integer_variable_states.resize(t.when);
    _imp->changed.clear();
    _imp->guesses.erase(_imp->guesses.begin() + t.how_many_guesses, _imp->guesses.end());
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

auto State::for_each_guess(function<auto (Literal) -> void> f) const -> void
{
    for (auto & g : _imp->guesses)
        f(g);
}

auto State::add_proof_steps(JustifyExplicitly why) -> void
{
    if (_imp->problem->optional_proof())
        why.add_proof_steps(*_imp->problem->optional_proof());
}

auto State::literal_is_nonfalsified(const Literal & lit) const -> bool
{
    return visit(overloaded {
        [&] (const LiteralFromIntegerVariable & ilit) -> bool {
            switch (ilit.state) {
                case LiteralFromIntegerVariable::Equal:
                    return in_domain(ilit.var, ilit.value);
                case LiteralFromIntegerVariable::Less:
                    return lower_bound(ilit.var) < ilit.value;
                case LiteralFromIntegerVariable::GreaterEqual:
                     return upper_bound(ilit.var) >= ilit.value;
                case LiteralFromIntegerVariable::NotEqual: {
                    auto single_value = optional_single_value(ilit.var);
                    return (nullopt == single_value || *single_value != ilit.value);
                }
            }

            throw NonExhaustiveSwitch{ };
        },
        [] (const TrueLiteral &) { return true; },
        [] (const FalseLiteral &) { return false; }
        }, lit);
}

auto State::test_literal(const Literal & lit) const -> LiteralIs
{
    return visit(overloaded {
        [&] (const LiteralFromIntegerVariable & ilit) -> LiteralIs {
            switch (ilit.state) {
                case LiteralFromIntegerVariable::Equal:
                    if (! in_domain(ilit.var, ilit.value))
                        return LiteralIs::DefinitelyFalse;
                    else if (optional_single_value(ilit.var))
                        return LiteralIs::DefinitelyTrue;
                    else
                        return LiteralIs::Undecided;

                case LiteralFromIntegerVariable::Less:
                    if (lower_bound(ilit.var) < ilit.value) {
                        if (upper_bound(ilit.var) < ilit.value)
                            return LiteralIs::DefinitelyTrue;
                        else
                            return LiteralIs::Undecided;
                    }
                    else
                        return LiteralIs::DefinitelyFalse;

                case LiteralFromIntegerVariable::GreaterEqual:
                    if (upper_bound(ilit.var) >= ilit.value) {
                        if (lower_bound(ilit.var) >= ilit.value)
                            return LiteralIs::DefinitelyTrue;
                        else
                            return LiteralIs::Undecided;
                    }
                    else
                        return LiteralIs::DefinitelyFalse;

                case LiteralFromIntegerVariable::NotEqual:
                    if (! in_domain(ilit.var, ilit.value))
                        return LiteralIs::DefinitelyTrue;
                    else if (optional_single_value(ilit.var))
                        return LiteralIs::DefinitelyFalse;
                    else
                        return LiteralIs::Undecided;
            }

            throw NonExhaustiveSwitch{ };
        },
        [] (const TrueLiteral &) { return LiteralIs::DefinitelyTrue; },
        [] (const FalseLiteral &) { return LiteralIs::DefinitelyFalse; }
        }, lit);
}

