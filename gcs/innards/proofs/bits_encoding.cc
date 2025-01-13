#include <gcs/innards/power.hh>
#include <gcs/innards/proofs/bits_encoding.hh>

#include <algorithm>
#include <bit>
#include <cstdlib>

using namespace gcs;
using namespace gcs::innards;

using std::bit_width;
using std::max;
using std::tuple;

auto gcs::innards::get_bits_encoding_coeffs(Integer lower, Integer upper) -> tuple<Integer, Integer, Integer>
{
    Integer highest_abs_value = max({abs(lower) - 1_i, abs(upper), 1_i});
    Integer highest_bit_shift = Integer{bit_width(static_cast<unsigned long long>(highest_abs_value.raw_value))} - 1_i;
    Integer highest_bit_coeff = power2(highest_bit_shift);
    auto negative_bit_coeff = lower < 0_i ? (-highest_bit_coeff * 2_i) : 0_i;
    return tuple{highest_bit_shift, highest_bit_coeff, negative_bit_coeff};
}
