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

TEST_CASE("count_setting: unset and empty take the default silently")
{
    CHECK(count_setting(nullptr, 42).value == 42ULL);
    CHECK(! count_setting(nullptr, 42).malformed);
    CHECK(count_setting("", 42).value == 42ULL);
    CHECK(! count_setting("", 42).malformed);
}

TEST_CASE("count_setting: a valid count is used")
{
    CHECK(count_setting("0", 42).value == 0ULL);
    CHECK(count_setting("7", 42).value == 7ULL);
    CHECK(! count_setting("7", 42).malformed);
}

TEST_CASE("count_setting: a malformed value takes the default and is marked")
{
    // These are what the caller warns about.
    for (const char * value : {"abc", "-5", " 5", "18446744073709551616"}) {
        CHECK(count_setting(value, 42).value == 42ULL);
        CHECK(count_setting(value, 42).malformed);
    }
}

TEST_CASE("count_as_long_long: clamps a count past long long")
{
    CHECK(count_as_long_long(0) == 0LL);
    CHECK(count_as_long_long(100000) == 100000LL);
    CHECK(count_as_long_long(static_cast<unsigned long long>(numeric_limits<long long>::max())) == numeric_limits<long long>::max());
    CHECK(count_as_long_long(static_cast<unsigned long long>(numeric_limits<long long>::max()) + 1) == numeric_limits<long long>::max());
    CHECK(count_as_long_long(numeric_limits<unsigned long long>::max()) == numeric_limits<long long>::max());
}
