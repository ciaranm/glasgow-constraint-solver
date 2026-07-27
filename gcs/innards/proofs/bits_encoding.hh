#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_BITS_ENCODING_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_BITS_ENCODING_HH

#include <gcs/integer.hh>

#include <tuple>

namespace gcs::innards
{
    /**
     * \brief Return the highest bit shift, highest bit coefficient, and negative bit
     * coefficient for a variable ranging from lower to upper.
     *
     * Only used inside proof innards. This is only in the API so it can be tested.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto get_bits_encoding_coeffs(Integer lower, Integer upper) -> std::tuple<Integer, Integer, Integer>;

    /**
     * \brief Can a variable ranging from lower to upper actually be given a
     * bits encoding, or would its coefficients overflow an Integer?
     *
     * FlatZinc's unbounded ints get bounds of half the Integer range, which
     * still encodes -- but a view negating such a variable can need one more
     * bit than exists. Callers introducing a bit vector for a *derived* range
     * check this first and fall back rather than overflow.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto bits_encoding_fits(Integer lower, Integer upper) -> bool;
}

#endif
