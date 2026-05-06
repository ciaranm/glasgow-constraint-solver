#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_POWER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_POWER_HH

#include <gcs/integer.hh>

#include <optional>

namespace gcs::innards
{
    [[nodiscard]] auto power2(Integer i) -> Integer;

    /**
     * \brief Integer base raised to integer exponent, with overflow checking.
     *
     * Returns std::nullopt if the result would overflow Integer's range, or if
     * no integer value exists for the operands (i.e. negative exponent with
     * |base| != 1, or 0 raised to a negative power). 0^0 is taken to be 1 by
     * convention.
     */
    [[nodiscard]] auto checked_integer_power(Integer base, Integer exp) -> std::optional<Integer>;
}

#endif
