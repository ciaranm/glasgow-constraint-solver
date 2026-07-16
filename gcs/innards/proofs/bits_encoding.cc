#include <gcs/innards/power.hh>
#include <gcs/innards/proofs/bits_encoding.hh>

#include <algorithm>
#include <bit>
#include <cstdlib>
#include <limits>

using namespace gcs;
using namespace gcs::innards;

using std::bit_width;
using std::max;
using std::tuple;

auto gcs::innards::get_bits_encoding_coeffs(Integer lower, Integer upper) -> tuple<Integer, Integer, Integer>
{
    // The positive side needs enough magnitude bits to reach `upper` -- which is
    // no constraint at all for a wholly-negative domain, so use the *signed*
    // upper, not abs(upper). Using abs(upper) over-allocates a magnitude bit for
    // negative singletons at powers of two (e.g. {-2} would get two magnitude
    // bits rather than one). The negative side is covered by abs(lower) - 1,
    // since the sign bit contributes -2^(shift+1). This matches the tight u+1
    // two's-complement width (Step 5 of Matthew's thesis).
    //
    // No magnitude bits are allocated unless they can reach a value the domain
    // contains: {-1} and {-1,0} are just the sign bit (the value is -1 * sign),
    // and {0} is the *empty* sum, identically zero, with no atoms at all -- its
    // bound rows print with an empty left-hand side, which veripb parses (since
    // the 2026-07-10 labelled-empty-LHS fix) and every ge/eq atom over it is a
    // pinned constant. This conforms to cake_pb_cp's width rule (issue #478);
    // the thesis's "least strictly positive h" floor (eq. 3.21) would instead
    // give {0} one magnitude bit, a divergence cake upstream asked us to drop
    // in preference to adding the floor to cake.
    Integer highest_abs_value = lower < 0_i ? max(abs(lower) - 1_i, upper) : upper;
    Integer highest_bit_shift = Integer{bit_width(static_cast<unsigned long long>(highest_abs_value.raw_value))} - 1_i;
    Integer highest_bit_coeff = highest_bit_shift >= 0_i ? power2(highest_bit_shift) : 0_i;
    auto negative_bit_coeff = lower < 0_i ? -power2(highest_bit_shift + 1_i) : 0_i;
    return tuple{highest_bit_shift, highest_bit_coeff, negative_bit_coeff};
}

auto gcs::innards::bits_encoding_fits(Integer lower, Integer upper) -> bool
{
    // Mirrors the arithmetic above, which materialises power2(highest_bit_shift)
    // and, for a negative lower bound, power2(highest_bit_shift + 1); power2
    // refuses anything that would overflow an Integer. Kept adjacent to
    // get_bits_encoding_coeffs so the two stay in agreement.
    if (lower == Integer::min_value())
        return false;
    Integer highest_abs_value = lower < 0_i ? max(abs(lower) - 1_i, upper) : upper;
    Integer highest_bit_shift = Integer{bit_width(static_cast<unsigned long long>(highest_abs_value.raw_value))} - 1_i;
    Integer highest_needed_power = lower < 0_i ? highest_bit_shift + 1_i : highest_bit_shift;
    return highest_needed_power < Integer{std::numeric_limits<long long>::digits};
}
