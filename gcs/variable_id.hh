/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_VARIABLE_ID_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_VARIABLE_ID_HH

#include <gcs/integer.hh>

#include <string>
#include <utility>
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

        [[nodiscard]] auto operator<=>(const SimpleIntegerVariableID &) const = default;
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

        [[nodiscard]] auto operator<=>(const ViewOfIntegerVariableID &) const = default;
    };

    struct ConstantIntegerVariableID
    {
        Integer const_value;

        explicit ConstantIntegerVariableID(Integer x) :
            const_value(x)
        {
        }

        [[nodiscard]] auto operator<=>(const ConstantIntegerVariableID &) const = default;
    };

    using IntegerVariableID = std::variant<SimpleIntegerVariableID, ViewOfIntegerVariableID, ConstantIntegerVariableID>;

    // The following is badly named... Maybe a good name will become evident once the variants
    // gain more items?
    using DirectIntegerVariableID = std::variant<SimpleIntegerVariableID, ConstantIntegerVariableID>;

    [[nodiscard]] inline auto constant_variable(const Integer x) -> IntegerVariableID
    {
        return ConstantIntegerVariableID{x};
    }

    [[nodiscard]] inline auto operator"" _c(unsigned long long v) -> ConstantIntegerVariableID
    {
        return ConstantIntegerVariableID{Integer(v)};
    }

    [[nodiscard]] inline auto operator-(ConstantIntegerVariableID a) -> ConstantIntegerVariableID
    {
        return ConstantIntegerVariableID{-a.const_value};
    }

    [[nodiscard]] auto operator+(IntegerVariableID v, Integer o) -> IntegerVariableID;

    [[nodiscard]] auto operator-(IntegerVariableID v, Integer o) -> IntegerVariableID;

    using VariableID = std::variant<IntegerVariableID>;
}

#endif
