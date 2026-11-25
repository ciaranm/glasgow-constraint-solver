#include <gcs/innards/environment.hh>

#include <catch2/catch_test_macros.hpp>

#include <limits>
#include <optional>

using namespace gcs::innards;

using std::nullopt;
using std::numeric_limits;

TEST_CASE("parse_non_negative_count: accepts a whole decimal count")
{
    CHECK(parse_non_negative_count("0") == 0ULL);
    CHECK(parse_non_negative_count("128") == 128ULL);
    CHECK(parse_non_negative_count("007") == 7ULL);
    CHECK(parse_non_negative_count("18446744073709551615") == numeric_limits<unsigned long long>::max());
}

TEST_CASE("parse_non_negative_count: refuses what strtoull would misread")
{
    // strtoull reads these as 0, a huge count, or a prefix.
    CHECK(parse_non_negative_count("") == nullopt);
    CHECK(parse_non_negative_count("abc") == nullopt);
    CHECK(parse_non_negative_count("-5") == nullopt);
    CHECK(parse_non_negative_count("+5") == nullopt);
    CHECK(parse_non_negative_count(" 5") == nullopt);
    CHECK(parse_non_negative_count("12x") == nullopt);
    CHECK(parse_non_negative_count("1e3") == nullopt);
    CHECK(parse_non_negative_count("18446744073709551616") == nullopt);
}
