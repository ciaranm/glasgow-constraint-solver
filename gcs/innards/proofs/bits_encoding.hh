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
    [[nodiscard]] auto get_bits_encoding_coeffs(Integer lower, Integer upper) -> std::tuple<int, Integer, Integer>;
}

#endif
