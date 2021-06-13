/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include "gcs/state.hh"
#include "gcs/exception.hh"

#include "util/overloaded.hh"

#include <vector>

using namespace gcs;

using std::make_shared;
using std::move;
using std::set;
using std::vector;
using std::visit;

struct State::Imp
{
    vector<IntegerVariable> integer_variables;
};

State::State() :
    _imp(new Imp)
{
}

State::State(State && other) = default;

State::~State() = default;

auto State::clone() const -> State
{
    State result;
    result._imp->integer_variables = _imp->integer_variables;
    return result;
}

auto State::allocate_integer_variable(Integer lower, Integer upper) -> IntegerVariableID
{
    _imp->integer_variables.push_back(IntegerRangeVariable{ lower, upper });
    return IntegerVariableID{ _imp->integer_variables.size() - 1 };
}

auto State::integer_variable(const IntegerVariableID i) -> IntegerVariable &
{
    return _imp->integer_variables[i.index];
}

auto State::integer_variable(const IntegerVariableID i) const -> const IntegerVariable &
{
    return _imp->integer_variables[i.index];
}

auto State::value_of(const IntegerVariableID i) const -> std::optional<Integer>
{
    return optional_single_value(integer_variable(i));
}

auto State::infer_boolean(const LiteralFromBooleanVariable &) -> Inference
{
    throw UnimplementedException{ };
}

auto State::infer_integer(const LiteralFromIntegerVariable & ilit) -> Inference
{
    switch (ilit.state) {
        case LiteralFromIntegerVariable::Equal:
            // Has to be equal. If the value isn't in the domain, we've found a
            // contradiction, otherwise update to a constant value.
            if (! in_domain(integer_variable(ilit.var), ilit.value))
                return Inference::NoChange;
            else if (optional_single_value(integer_variable(ilit.var)))
                return Inference::NoChange;
            else {
                integer_variable(ilit.var) = IntegerConstant{ ilit.value };
                return Inference::Change;
            }

        case LiteralFromIntegerVariable::NotEqual:
            // If the value isn't in the domain, we don't need to do anything.
            // Otherwise...
            if (! in_domain(integer_variable(ilit.var), ilit.value))
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
                                integer_variable(ilit.var) = IntegerConstant{ rvar.lower };
                            return Inference::Change;
                        }
                        else if (rvar.upper == ilit.value) {
                            --rvar.upper;

                            if (rvar.lower == rvar.upper)
                                integer_variable(ilit.var) = IntegerConstant{ rvar.lower };
                            return Inference::Change;
                        }
                        else {
                            // Holey domain, convert to set.
                            // This should handle larger ranges.
                            if (rvar.upper >= Integer{ Bits::number_of_bits })
                                throw UnimplementedException{ };

                            IntegerSmallSetVariable svar{ Integer{ 0 }, Bits{ 0 } };
                            for (Integer v = rvar.lower ; v <= rvar.upper ; ++v)
                                if (v != ilit.value)
                                    svar.bits.set(v.raw_value);
                            integer_variable(ilit.var) = move(svar);
                            return Inference::Change;
                        }
                    },
                    [&] (IntegerSmallSetVariable & svar) -> Inference {
                        // Knock out the value
                        svar.bits.reset(ilit.value.raw_value);
                        if (svar.bits.has_single_bit())
                            integer_variable(ilit.var) = IntegerConstant{ svar.lower + Integer{ svar.bits.countr_zero() } };
                        else if (svar.bits.none())
                            return Inference::Contradiction;
                        return Inference::Change;
                    },
                    [&] (IntegerSetVariable & svar) -> Inference {
                        // Knock out the value
                        if (1 == svar.values->size())
                            return Inference::Contradiction;
                        else if (2 == svar.values->size()) {
                            integer_variable(ilit.var) = IntegerConstant{ ilit.value == *svar.values->begin() ? *next(svar.values->begin()) : *svar.values->begin() };
                            return Inference::Change;
                        }
                        else {
                            auto new_values = make_shared<set<Integer> >(*svar.values);
                            new_values->erase(ilit.value);
                            svar.values = new_values;
                            return Inference::Change;
                        }
                    }
                }, integer_variable(ilit.var));

        case LiteralFromIntegerVariable::Less:
            return visit(overloaded {
                    [&] (IntegerConstant & c) -> Inference {
                        // Ok if the constant is less, otherwise contradiction
                        return c.value < ilit.value ? Inference::NoChange : Inference::Contradiction;
                    },
                    [&] (IntegerRangeVariable & rvar) -> Inference {
                        bool changed = false;
                        if (rvar.upper > ilit.value) {
                            changed = true;
                            rvar.upper = ilit.value;
                        }
                        if (rvar.lower == rvar.upper)
                            integer_variable(ilit.var) = IntegerConstant{ rvar.lower };
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
                            integer_variable(ilit.var) = IntegerConstant{ *optional_single_value(integer_variable(ilit.var)) };
                        return pc_before == pc_after ? Inference::NoChange : Inference::Change;
                    },
                    [&] (IntegerSetVariable &) -> Inference {
                        throw UnimplementedException{ };
                    }
                }, integer_variable(ilit.var));
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
                            integer_variable(ilit.var) = IntegerConstant{ rvar.lower };
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
                            integer_variable(ilit.var) = IntegerConstant{ *optional_single_value(integer_variable(ilit.var)) };
                        return pc_before == pc_after ? Inference::NoChange : Inference::Change;
                    },
                    [&] (IntegerSetVariable &) -> Inference {
                        throw UnimplementedException{ };
                    }
                }, integer_variable(ilit.var));
            break;
    }

    throw NonExhaustiveSwitch{ };
}

auto State::infer(const Literal & lit) -> Inference
{
    auto result = visit(overloaded {
            [&] (const LiteralFromBooleanVariable & blit) -> Inference {
                return infer_boolean(blit);
            },
            [&] (const LiteralFromIntegerVariable & ilit) -> Inference {
                return infer_integer(ilit);
            }
            }, lit);

    return result;
}

