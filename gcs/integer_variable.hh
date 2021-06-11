/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INTEGER_VARIABLE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INTEGER_VARIABLE_HH 1

#include <gcs/bits.hh>
#include <gcs/integer.hh>

#include <optional>
#include <variant>

namespace gcs
{
    struct IntegerVariableID
    {
        unsigned long long index;

        explicit IntegerVariableID(unsigned long long x) :
            index(x)
        {
        }

        [[ nodiscard ]] auto operator <=> (const IntegerVariableID &) const = default;
    };

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

    using IntegerVariable = std::variant<IntegerConstant, IntegerRangeVariable, IntegerSmallSetVariable>;

    [[ nodiscard ]] auto lower_bound(const IntegerVariable &) -> Integer;
    [[ nodiscard ]] auto upper_bound(const IntegerVariable &) -> Integer;
    [[ nodiscard ]] auto in_domain(const IntegerVariable &, Integer) -> bool;
    [[ nodiscard ]] auto optional_single_value(const IntegerVariable &) -> std::optional<Integer>;
    [[ nodiscard ]] auto domain_size(const IntegerVariable &) -> Integer;
}

#endif
