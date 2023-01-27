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
    /**
     * \brief Specifies that an IntegerVariableID has a constant value.
     *
     * \ingroup Innards
     * \sa State::state_of()
     */
    struct IntegerVariableConstantState
    {
        Integer value;

        explicit IntegerVariableConstantState(Integer v) :
            value(v)
        {
        }
    };

    /**
     * \brief Specifies that an IntegerVariableID has the values between lower and
     * upper inclusive.
     *
     * \ingroup Innards
     * \sa State::state_of()
     */
    struct IntegerVariableRangeState
    {
        Integer lower, upper;

        explicit IntegerVariableRangeState(Integer l, Integer u) :
            lower(l),
            upper(u)
        {
        }
    };

    /**
     * \brief Specifies that an IntegerVariableID has the values specified by
     * the bits, indexed with the first bit being lower.
     *
     * \ingroup Innards
     * \sa State::state_of()
     */
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

    /**
     * \brief Specifies that an IntegerVariableID has the values contained
     * in this set.
     *
     * \ingroup Innards
     * \sa State::state_of()
     */
    struct IntegerVariableSetState
    {
        std::shared_ptr<std::set<Integer>> values;

        explicit IntegerVariableSetState(std::shared_ptr<std::set<Integer>> v) :
            values(v)
        {
        }
    };

    /**
     * \brief An IntegerVariableID's values could be given in any of these
     * forms.
     *
     * \ingroup Innards
     * \sa State::state_of()
     */
    using IntegerVariableState = std::variant<
        IntegerVariableConstantState,
        IntegerVariableRangeState,
        IntegerVariableSmallSetState,
        IntegerVariableSetState>;

    /**
     * \brief Turn an IntegerVariableState into a semi-readable string for
     * debugging purposes.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto debug_string(const IntegerVariableState &) -> std::string;
}

#endif
