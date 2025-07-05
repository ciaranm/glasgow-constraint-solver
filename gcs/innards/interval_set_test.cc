#include <gcs/innards/interval_set.hh>

#include <catch2/catch_test_macros.hpp>

using namespace gcs;
using namespace gcs::innards;

using std::pair;
using std::vector;

namespace
{
    template <typename T_>
    auto intervals_of(const IntervalSet<T_> & i) -> vector<pair<T_, T_>>
    {
        vector<pair<T_, T_>> result;
        for (auto [l, u] : i.each_interval())
            result.emplace_back(l, u);
        return result;
    }
}

TEST_CASE("Interval set")
{
    IntervalSet<int> set(5, 10);
    CHECK(! set.empty());
    CHECK(set.size() == 6);
    CHECK(set.lower() == 5);
    CHECK(set.upper() == 10);
    for (int i = 5; i <= 10; ++i)
        CHECK(set.contains(i));
}

TEST_CASE("Erase start")
{
    IntervalSet<int> set(5, 10);
    set.erase(5);
    CHECK(set.size() == 5);
    CHECK(set.lower() == 6);
    CHECK(set.upper() == 10);
    for (int i = 5; i <= 10; ++i)
        CHECK(set.contains(i) == (i != 5));
}

TEST_CASE("Erase middle")
{
    IntervalSet<int> set(5, 10);
    set.erase(7);
    CHECK(set.size() == 5);
    CHECK(set.lower() == 5);
    CHECK(set.upper() == 10);
    for (int i = 5; i <= 10; ++i)
        CHECK(set.contains(i) == (i != 7));
}

TEST_CASE("Erase end")
{
    IntervalSet<int> set(5, 10);
    set.erase(10);
    CHECK(set.size() == 5);
    CHECK(set.lower() == 5);
    CHECK(set.upper() == 9);
    for (int i = 5; i <= 10; ++i)
        CHECK(set.contains(i) == (i != 10));
}

TEST_CASE("Erase less than")
{
    IntervalSet<int> set(5, 10);
    set.erase_less_than(7);
    CHECK(set.size() == 4);
    CHECK(set.lower() == 7);
    CHECK(set.upper() == 10);
    for (int i = 5; i <= 10; ++i)
        CHECK(set.contains(i) == (i >= 7));
}

TEST_CASE("Erase greater than")
{
    IntervalSet<int> set(5, 10);
    set.erase_greater_than(7);
    CHECK(set.size() == 3);
    CHECK(set.lower() == 5);
    CHECK(set.upper() == 7);
    for (int i = 5; i <= 10; ++i)
        CHECK(set.contains(i) == (i <= 7));
}

TEST_CASE("Erase greater than range")
{
    IntervalSet<int> set(-5, 5);
    set.erase(-1);
    set.erase(0);
    set.erase(1);
    CHECK(set.size() == 8);
    CHECK(set.lower() == -5);
    CHECK(set.upper() == 5);
    set.erase_greater_than(0);
    CHECK(set.size() == 4);
    CHECK(set.lower() == -5);
    CHECK(set.upper() == -2);
    for (int i = -5; i <= 5; ++i)
        CHECK(set.contains(i) == (i <= -2));
}

TEST_CASE("Erase less than range")
{
    IntervalSet<int> set(-5, 5);
    set.erase(-1);
    set.erase(0);
    set.erase(1);
    CHECK(set.size() == 8);
    CHECK(set.lower() == -5);
    CHECK(set.upper() == 5);
    set.erase_less_than(0);
    CHECK(set.size() == 4);
    CHECK(set.lower() == 2);
    CHECK(set.upper() == 5);
    for (int i = -5; i <= 5; ++i)
        CHECK(set.contains(i) == (i >= 2));
}

TEST_CASE("Poking holes")
{
    IntervalSet<int> set(1, 12);
    set.erase(3);
    set.erase_greater_than(10);
    set.erase(7);

    CHECK(intervals_of(set) == vector<pair<int, int>>{{1, 2}, {4, 6}, {8, 10}});
    for (int i = 1; i <= 12; ++i)
        CHECK(set.contains(i) == (i == 1 || i == 2 || i == 4 || i == 5 || i == 6 || i == 8 || i == 9 || i == 10));

    set.erase_less_than(6);
    CHECK(intervals_of(set) == vector<pair<int, int>>{{6, 6}, {8, 10}});

    for (int i = 1; i <= 12; ++i)
        CHECK(set.contains(i) == (i == 6 || i == 8 || i == 9 || i == 10));
}

TEST_CASE("Poking more holes")
{
    IntervalSet<int> set(1, 12);
    set.erase(3);
    set.erase_greater_than(10);
    set.erase(7);

    CHECK(intervals_of(set) == vector<pair<int, int>>{{1, 2}, {4, 6}, {8, 10}});
    set.erase_greater_than(5);
    CHECK(intervals_of(set) == vector<pair<int, int>>{{1, 2}, {4, 5}});

    for (int i = 1; i <= 12; ++i)
        CHECK(set.contains(i) == (i == 1 || i == 2 || i == 4 || i == 5));
}

TEST_CASE("Wipeout from below")
{
    IntervalSet<int> set(5, 10);
    set.erase_greater_than(2);
    CHECK(set.size() == 0);
    CHECK(intervals_of(set) == vector<pair<int, int>>{});
}

TEST_CASE("Wipeout from above")
{
    IntervalSet<int> set(5, 10);
    set.erase_less_than(12);
    CHECK(set.size() == 0);
    CHECK(intervals_of(set) == vector<pair<int, int>>{});
}

TEST_CASE("Erase on bounds")
{
    IntervalSet<int> set(1, 6);
    set.erase_greater_than(6);
    set.erase_less_than(1);
    CHECK(set.size() == 6);
    CHECK(intervals_of(set) == vector<pair<int, int>>{{1, 6}});
    set.erase_greater_than(5);
    set.erase_less_than(2);
    CHECK(set.size() == 4);
    CHECK(intervals_of(set) == vector<pair<int, int>>{{2, 5}});
    set.erase(2);
    CHECK(set.size() == 3);
    CHECK(intervals_of(set) == vector<pair<int, int>>{{3, 5}});
    set.erase(5);
    CHECK(set.size() == 2);
    CHECK(intervals_of(set) == vector<pair<int, int>>{{3, 4}});
}

TEST_CASE("Contains any of")
{
    IntervalSet<int> set1(5, 10), set2(3, 6), set3(8, 11), set4(6, 8);
    for (const auto & s1 : vector{set1, set2, set3, set4})
        for (const auto & s2 : vector{set1, set2, set3, set4}) {
            bool any = false;
            for (const auto & v : s1.each())
                for (const auto & w : s2.each())
                    if (v == w)
                        any = true;

            CHECK(s1.contains_any_of(s2) == any);
        }
}
