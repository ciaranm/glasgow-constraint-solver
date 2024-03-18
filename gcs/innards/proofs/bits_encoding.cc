#include <gcs/innards/proofs/bits_encoding.hh>

#include <algorithm>
#include <bit>
#include <cstdlib>

using namespace gcs;
using namespace gcs::innards;

using std::bit_ceil;
using std::countr_zero;
using std::max;
using std::tuple;

auto gcs::innards::get_bits_encoding_coeffs(Integer lower, Integer upper) -> tuple<int, Integer, Integer>
{
    Integer highest_abs_value = max({abs(lower), abs(upper) + 1_i, 2_i});
    int highest_bit_shift = countr_zero(bit_ceil(static_cast<unsigned long long>(highest_abs_value.raw_value))) - 1;
    Integer highest_bit_coeff = Integer{1ll << highest_bit_shift};
    auto negative_bit_coeff = lower < 0_i ? (-highest_bit_coeff * 2_i) : 0_i;
    return tuple{highest_bit_shift, highest_bit_coeff, negative_bit_coeff};
}
