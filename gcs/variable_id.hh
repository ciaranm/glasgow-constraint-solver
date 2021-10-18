/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_VARIABLE_ID_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_VARIABLE_ID_HH 1

#include <gcs/integer.hh>

#include <variant>

namespace gcs
{
    struct SimpleIntegerVariableID
    {
        unsigned long long index;

        explicit SimpleIntegerVariableID(unsigned long long x) :
            index(x)
        {
        }

        [[ nodiscard ]] auto operator <=> (const SimpleIntegerVariableID &) const = default;
    };

    struct ConstantIntegerVariableID
    {
        Integer const_value;

        explicit ConstantIntegerVariableID(Integer x) :
            const_value(x)
        {
        }

        [[ nodiscard ]] auto operator <=> (const ConstantIntegerVariableID &) const = default;
    };

    using IntegerVariableID = std::variant<SimpleIntegerVariableID, ConstantIntegerVariableID>;

    [[ nodiscard ]] inline auto constant_variable(const Integer x) -> IntegerVariableID
    {
        return ConstantIntegerVariableID(x);
    }

    [[ nodiscard ]] inline auto operator "" _c (unsigned long long v) -> IntegerVariableID
    {
        return constant_variable(Integer(v));
    }

    [[ nodiscard ]] auto debug_string(const IntegerVariableID &) -> std::string;

    using VariableID = std::variant<IntegerVariableID>;

    [[ nodiscard ]] auto debug_string(const VariableID &) -> std::string;
}

#endif
