/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INTEGER_VARIABLE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INTEGER_VARIABLE_HH 1

#include <gcs/bits.hh>
#include <gcs/integer.hh>

#include <memory>
#include <optional>
#include <set>
#include <string>
#include <variant>

namespace gcs
{
    struct IntegerVariableID
    {
        std::variant<unsigned long long, Integer> index_or_const_value;

        explicit IntegerVariableID(unsigned long long x) :
            index_or_const_value(x)
        {
        }

        explicit IntegerVariableID(Integer x) :
            index_or_const_value(x)
        {
        }

        [[ nodiscard ]] auto operator <=> (const IntegerVariableID &) const = default;
    };

    [[ nodiscard ]] inline auto constant_variable(const Integer x) -> IntegerVariableID
    {
        return IntegerVariableID(x);
    }

    [[ nodiscard ]] inline auto operator "" _c (unsigned long long v) -> IntegerVariableID
    {
        return constant_variable(Integer(v));
    }

    struct IntegerConstant
    {
        Integer value;

        explicit IntegerConstant(Integer v) :
            value(v)
        {
        }
    };

    struct IntegerRangeVariable
    {
        Integer lower, upper;

        explicit IntegerRangeVariable(Integer l, Integer u) :
            lower(l),
            upper(u)
        {
        }
    };

    struct IntegerSmallSetVariable
    {
        Integer lower;
        Bits bits;

        explicit IntegerSmallSetVariable(Integer l, Bits b) :
            lower(l),
            bits(b)
        {
        }
    };

    struct IntegerSetVariable
    {
        std::shared_ptr<std::set<Integer> > values;

        explicit IntegerSetVariable(std::shared_ptr<std::set<Integer> > v) :
            values(v)
        {
        }
    };

    using IntegerVariable = std::variant<IntegerConstant, IntegerRangeVariable, IntegerSmallSetVariable, IntegerSetVariable>;

    [[ nodiscard ]] auto debug_string(const IntegerVariable &) -> std::string;
    [[ nodiscard ]] auto debug_string(const IntegerVariableID &) -> std::string;
}

#endif
