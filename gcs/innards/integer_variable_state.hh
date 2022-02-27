/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INTEGER_VARIABLE_STATE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INTEGER_VARIABLE_STATE_HH

#include <gcs/innards/bits.hh>
#include <gcs/integer.hh>

#include <memory>
#include <optional>
#include <set>
#include <string>
#include <variant>

namespace gcs::innards
{
    struct IntegerVariableConstantState
    {
        Integer value;

        explicit IntegerVariableConstantState(Integer v) :
            value(v)
        {
        }
    };

    struct IntegerVariableRangeState
    {
        Integer lower, upper;

        explicit IntegerVariableRangeState(Integer l, Integer u) :
            lower(l),
            upper(u)
        {
        }
    };

    struct IntegerVariableSmallSetState
    {
        Integer lower;
        Bits bits;

        explicit IntegerVariableSmallSetState(Integer l, Bits b) :
            lower(l),
            bits(b)
        {
        }
    };

    struct IntegerVariableSetState
    {
        std::shared_ptr<std::set<Integer>> values;

        explicit IntegerVariableSetState(std::shared_ptr<std::set<Integer>> v) :
            values(v)
        {
        }
    };

    using IntegerVariableState = std::variant<
        IntegerVariableConstantState,
        IntegerVariableRangeState,
        IntegerVariableSmallSetState,
        IntegerVariableSetState>;

    [[nodiscard]] auto debug_string(const IntegerVariableState &) -> std::string;
}

#endif
