/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_VARIABLE_ID_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_VARIABLE_ID_HH 1

#include <gcs/integer.hh>

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

    [[ nodiscard ]] auto debug_string(const IntegerVariableID &) -> std::string;

    struct BooleanVariableID
    {
        std::variant<unsigned long long, bool> index_or_const_value;

        explicit BooleanVariableID(unsigned long long x) :
            index_or_const_value(x)
        {
        }

        explicit BooleanVariableID(bool x) :
            index_or_const_value(x)
        {
        }
    };

    [[ nodiscard ]] inline auto constant_variable(bool x) -> BooleanVariableID
    {
        return BooleanVariableID(x);
    }

    using VariableID = std::variant<IntegerVariableID, BooleanVariableID>;
}

#endif
