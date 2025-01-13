#include <gcs/innards/proofs/bits_encoding.hh>
#include <gcs/integer.hh>

#include <catch2/catch_test_macros.hpp>

using namespace gcs;
using namespace gcs::innards;

using std::tuple;

TEST_CASE("Bit encodings")
{
    CHECK(get_bits_encoding_coeffs(0_i, 1_i) == tuple{0_i, 1_i, 0_i});
    CHECK(get_bits_encoding_coeffs(0_i, 2_i) == tuple{1_i, 2_i, 0_i});
    CHECK(get_bits_encoding_coeffs(0_i, 3_i) == tuple{1_i, 2_i, 0_i});
    CHECK(get_bits_encoding_coeffs(0_i, 4_i) == tuple{2_i, 4_i, 0_i});
    CHECK(get_bits_encoding_coeffs(0_i, 5_i) == tuple{2_i, 4_i, 0_i});
    CHECK(get_bits_encoding_coeffs(0_i, 6_i) == tuple{2_i, 4_i, 0_i});
    CHECK(get_bits_encoding_coeffs(0_i, 7_i) == tuple{2_i, 4_i, 0_i});
    CHECK(get_bits_encoding_coeffs(0_i, 8_i) == tuple{3_i, 8_i, 0_i});
    CHECK(get_bits_encoding_coeffs(0_i, 9_i) == tuple{3_i, 8_i, 0_i});

    CHECK(get_bits_encoding_coeffs(1_i, 9_i) == tuple{3_i, 8_i, 0_i});

    CHECK(get_bits_encoding_coeffs(-1_i, 0_i) == tuple{0_i, 1_i, -2_i});
    CHECK(get_bits_encoding_coeffs(-2_i, 0_i) == tuple{0_i, 1_i, -2_i});
    CHECK(get_bits_encoding_coeffs(-3_i, 0_i) == tuple{1_i, 2_i, -4_i});

    CHECK(get_bits_encoding_coeffs(-1_i, 1_i) == tuple{0_i, 1_i, -2_i});
    CHECK(get_bits_encoding_coeffs(-2_i, 1_i) == tuple{0_i, 1_i, -2_i});
    CHECK(get_bits_encoding_coeffs(-3_i, 1_i) == tuple{1_i, 2_i, -4_i});
    CHECK(get_bits_encoding_coeffs(-4_i, 1_i) == tuple{1_i, 2_i, -4_i});
    CHECK(get_bits_encoding_coeffs(-5_i, 1_i) == tuple{2_i, 4_i, -8_i});
    CHECK(get_bits_encoding_coeffs(-6_i, 1_i) == tuple{2_i, 4_i, -8_i});
    CHECK(get_bits_encoding_coeffs(-7_i, 1_i) == tuple{2_i, 4_i, -8_i});
    CHECK(get_bits_encoding_coeffs(-8_i, 1_i) == tuple{2_i, 4_i, -8_i});
    CHECK(get_bits_encoding_coeffs(-9_i, 1_i) == tuple{3_i, 8_i, -16_i});

    CHECK(get_bits_encoding_coeffs(-1_i, 7_i) == tuple{2_i, 4_i, -8_i});
    CHECK(get_bits_encoding_coeffs(-2_i, 7_i) == tuple{2_i, 4_i, -8_i});
    CHECK(get_bits_encoding_coeffs(-3_i, 7_i) == tuple{2_i, 4_i, -8_i});
    CHECK(get_bits_encoding_coeffs(-4_i, 7_i) == tuple{2_i, 4_i, -8_i});
    CHECK(get_bits_encoding_coeffs(-5_i, 7_i) == tuple{2_i, 4_i, -8_i});
    CHECK(get_bits_encoding_coeffs(-6_i, 7_i) == tuple{2_i, 4_i, -8_i});
    CHECK(get_bits_encoding_coeffs(-7_i, 7_i) == tuple{2_i, 4_i, -8_i});
    CHECK(get_bits_encoding_coeffs(-8_i, 7_i) == tuple{2_i, 4_i, -8_i});
    CHECK(get_bits_encoding_coeffs(-9_i, 7_i) == tuple{3_i, 8_i, -16_i});

    CHECK(get_bits_encoding_coeffs(-3_i, -3_i) == tuple{1_i, 2_i, -4_i});
    CHECK(get_bits_encoding_coeffs(-4_i, -3_i) == tuple{1_i, 2_i, -4_i});
    CHECK(get_bits_encoding_coeffs(-5_i, -3_i) == tuple{2_i, 4_i, -8_i});
    CHECK(get_bits_encoding_coeffs(-6_i, -3_i) == tuple{2_i, 4_i, -8_i});
    CHECK(get_bits_encoding_coeffs(-7_i, -3_i) == tuple{2_i, 4_i, -8_i});
    CHECK(get_bits_encoding_coeffs(-8_i, -3_i) == tuple{2_i, 4_i, -8_i});
    CHECK(get_bits_encoding_coeffs(-9_i, -3_i) == tuple{3_i, 8_i, -16_i});
}
