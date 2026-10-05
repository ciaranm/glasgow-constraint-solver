#include <gcs/innards/integer_overflow.hh>
#include <gcs/innards/power.hh>
#include <gcs/innards/wide_sum.hh>
#include <gcs/integer.hh>

#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include <climits>

using namespace gcs;
using Catch::Matchers::EndsWith;
using gcs::innards::IntegerOverflow;
using gcs::innards::power2;
using gcs::innards::WideSum;

TEST_CASE("Integer arithmetic on normal values")
{
    REQUIRE((3_i + 4_i).raw_value == 7);
    REQUIRE((10_i - 4_i).raw_value == 6);
    REQUIRE((6_i * 7_i).raw_value == 42);
    REQUIRE((20_i / 3_i).raw_value == 6);
    REQUIRE((20_i % 3_i).raw_value == 2);
    REQUIRE((-5_i).raw_value == -5);
    REQUIRE(abs(Integer{-7}).raw_value == 7);

    Integer x{5};
    x += 3_i;
    REQUIRE(x.raw_value == 8);
    x -= 2_i;
    REQUIRE(x.raw_value == 6);

    Integer y{0};
    REQUIRE((++y).raw_value == 1);
    REQUIRE((y++).raw_value == 1);
    REQUIRE(y.raw_value == 2);
    REQUIRE((--y).raw_value == 1);
    REQUIRE((y--).raw_value == 1);
    REQUIRE(y.raw_value == 0);
}

TEST_CASE("Integer overflow on addition")
{
    REQUIRE_THROWS_AS(Integer::max_value() + 1_i, IntegerOverflow);
    REQUIRE_THROWS_AS(Integer::min_value() + Integer{-1}, IntegerOverflow);

    Integer x = Integer::max_value();
    REQUIRE_THROWS_AS(x += 1_i, IntegerOverflow);
}

TEST_CASE("Integer overflow on subtraction")
{
    REQUIRE_THROWS_AS(Integer::min_value() - 1_i, IntegerOverflow);
    REQUIRE_THROWS_AS(Integer::max_value() - Integer{-1}, IntegerOverflow);

    Integer x = Integer::min_value();
    REQUIRE_THROWS_AS(x -= 1_i, IntegerOverflow);
}

TEST_CASE("Integer overflow reports its operands, and leaves a compound assignment's target alone")
{
    // The operands, not the wrapped result: min_value() + -2^61 wraps to 3 * 2^61,
    // which a compound assignment used to report as its left operand (issue #1003).
    auto big = Integer{-(1LL << 61)};
    REQUIRE_THROWS_WITH(Integer::min_value() + big, EndsWith("Integer overflow: -9223372036854775808 + -2305843009213693952"));
    REQUIRE_THROWS_WITH(Integer::max_value() - Integer{-1}, EndsWith("Integer overflow: 9223372036854775807 - -1"));

    Integer x = Integer::min_value();
    REQUIRE_THROWS_WITH(x += big, EndsWith("Integer overflow: -9223372036854775808 += -2305843009213693952"));
    REQUIRE(x == Integer::min_value());

    Integer y = Integer::max_value();
    REQUIRE_THROWS_WITH(y -= Integer{-1}, EndsWith("Integer overflow: 9223372036854775807 -= -1"));
    REQUIRE(y == Integer::max_value());
}

TEST_CASE("Integer overflow on multiplication")
{
    REQUIRE_THROWS_AS(Integer::max_value() * 2_i, IntegerOverflow);
    REQUIRE_THROWS_AS(Integer::min_value() * 2_i, IntegerOverflow);
    REQUIRE_THROWS_AS(Integer::min_value() * Integer{-1}, IntegerOverflow);
}

TEST_CASE("Integer division edge cases")
{
    REQUIRE_THROWS_AS(7_i / 0_i, IntegerOverflow);
    REQUIRE_THROWS_AS(0_i / 0_i, IntegerOverflow);
    REQUIRE_THROWS_AS(Integer::min_value() / Integer{-1}, IntegerOverflow);

    REQUIRE_THROWS_AS(7_i % 0_i, IntegerOverflow);
    REQUIRE_THROWS_AS(Integer::min_value() % Integer{-1}, IntegerOverflow);
}

TEST_CASE("Integer unary minus and abs edge cases")
{
    REQUIRE_THROWS_AS(-Integer::min_value(), IntegerOverflow);
    REQUIRE_THROWS_AS(abs(Integer::min_value()), IntegerOverflow);
}

TEST_CASE("Integer increment and decrement at limits")
{
    Integer at_max = Integer::max_value();
    REQUIRE_THROWS_AS(++at_max, IntegerOverflow);

    Integer also_at_max = Integer::max_value();
    REQUIRE_THROWS_AS(also_at_max++, IntegerOverflow);

    Integer at_min = Integer::min_value();
    REQUIRE_THROWS_AS(--at_min, IntegerOverflow);

    Integer also_at_min = Integer::min_value();
    REQUIRE_THROWS_AS(also_at_min--, IntegerOverflow);
}

TEST_CASE("The bounded range is symmetric, and require_bounded checks it")
{
    REQUIRE(Integer::min_bounded_value() == -Integer::max_bounded_value());
    REQUIRE(innards::require_bounded(Integer::max_bounded_value(), "x") == Integer::max_bounded_value());
    REQUIRE(innards::require_bounded(Integer::min_bounded_value(), "x") == Integer::min_bounded_value());
    REQUIRE_THROWS_AS(innards::require_bounded(Integer::max_bounded_value() + 1_i, "x"), IntegerOverflow);
    REQUIRE_THROWS_AS(innards::require_bounded(Integer::min_bounded_value() - 1_i, "x"), IntegerOverflow);
}

TEST_CASE("power2 past the top of Integer is an overflow")
{
    // Issue #202: this used to be an UnimplementedException.
    REQUIRE(power2(62_i) == Integer{1LL << 62});
    REQUIRE_THROWS_AS(power2(63_i), IntegerOverflow);
}

TEST_CASE("WideSum is exact whatever order the terms come in")
{
    const auto B = Integer::max_bounded_value(), A = Integer::min_bounded_value();
    WideSum grouped;
    for (int i = 0; i < 9; ++i)
        grouped += B;
    REQUIRE(! grouped.narrow());
    REQUIRE_THROWS_AS(grouped.narrow_or_throw(), IntegerOverflow);
    for (int i = 0; i < 9; ++i)
        grouped += A;
    REQUIRE(grouped.narrow() == 0_i);

    WideSum low{Integer::min_value()};
    low -= 1_i;
    REQUIRE(! low.narrow());
    REQUIRE(low < Integer::min_value());
    low += 1_i;
    REQUIRE(low.narrow() == Integer::min_value());
    REQUIRE((-low) > Integer::max_value());
    REQUIRE((-(-low)).narrow() == Integer::min_value());

    REQUIRE(WideSum{Integer::max_value()} + 1_i > WideSum{Integer::max_value()});
    REQUIRE(WideSum{-5_i} < WideSum{3_i});
    REQUIRE(WideSum{-5_i} == -5_i);
}

TEST_CASE("WideSum divides exactly, past Integer's range too")
{
    const auto two_to_the_60 = Integer{1LL << 60};
    REQUIRE(WideSum{12_i}.divided_exactly_by(4_i) == 3_i);
    REQUIRE(WideSum{12_i}.divided_exactly_by(-4_i) == -3_i);
    REQUIRE(! WideSum{13_i}.divided_exactly_by(4_i));
    REQUIRE(! WideSum{13_i}.divided_exactly_by(0_i));
    REQUIRE(! WideSum{Integer::min_value()}.divided_exactly_by(-1_i));

    // 2^64 is past Integer's range, but 2^64 / 2^60 is 16.
    WideSum two_to_the_64;
    for (int i = 0; i < 16; ++i)
        two_to_the_64 += two_to_the_60;
    REQUIRE(! two_to_the_64.narrow());
    REQUIRE(two_to_the_64.divided_exactly_by(two_to_the_60) == 16_i);
    REQUIRE((-two_to_the_64).divided_exactly_by(two_to_the_60) == -16_i);
    REQUIRE(two_to_the_64.divided_exactly_by(-two_to_the_60) == -16_i);
    REQUIRE(! (two_to_the_64 + 1_i).divided_exactly_by(two_to_the_60));
    // A quotient that does not fit is refused.
    REQUIRE(! two_to_the_64.divided_exactly_by(2_i));
}
