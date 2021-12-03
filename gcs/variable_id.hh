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

    struct ViewOfIntegerVariableID
    {
        SimpleIntegerVariableID actual_variable;
        Integer offset;

        explicit ViewOfIntegerVariableID(SimpleIntegerVariableID a, Integer o) :
            actual_variable(a),
            offset(o)
        {
        }

        [[ nodiscard ]] auto operator <=> (const ViewOfIntegerVariableID &) const = default;
    };

    [[ nodiscard ]] inline auto operator+ (SimpleIntegerVariableID v, Integer o) -> ViewOfIntegerVariableID
    {
        return ViewOfIntegerVariableID{ v, o };
    }

    [[ nodiscard ]] inline auto operator- (SimpleIntegerVariableID v, Integer o) -> ViewOfIntegerVariableID
    {
        return ViewOfIntegerVariableID{ v, -o };
    }

    struct ConstantIntegerVariableID
    {
        Integer const_value;

        explicit ConstantIntegerVariableID(Integer x) :
            const_value(x)
        {
        }

        [[ nodiscard ]] auto operator <=> (const ConstantIntegerVariableID &) const = default;
    };

    using IntegerVariableID = std::variant<SimpleIntegerVariableID, ViewOfIntegerVariableID, ConstantIntegerVariableID>;

    // The following is badly named... Maybe a good name will become evident once the variants
    // gain more items?
    using DirectIntegerVariableID = std::variant<SimpleIntegerVariableID, ConstantIntegerVariableID>;

    [[ nodiscard ]] auto underlying_direct_variable_and_offset(const IntegerVariableID var) -> std::pair<DirectIntegerVariableID, Integer>;

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
