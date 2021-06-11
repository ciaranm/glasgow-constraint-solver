/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include "gcs/state.hh"
#include "gcs/exception.hh"

#include "util/overloaded.hh"

#include <vector>

using namespace gcs;

using std::move;
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
                    }
                }, integer_variable(ilit.var));

        default:
            throw UnimplementedException{ };
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

