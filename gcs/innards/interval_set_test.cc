#include <gcs/innards/interval_set.hh>

#include <catch2/catch_test_macros.hpp>

#include <algorithm>

using namespace gcs;
using namespace gcs::innards;

using std::pair;
using std::ranges::reverse;
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

TEST_CASE("Default-constructed set is empty")
{
    IntervalSet<int> set;
    CHECK(set.empty());
    CHECK(set.size() == 0);
    CHECK(! set.contains(0));
    CHECK(intervals_of(set) == vector<pair<int, int>>{});
}

TEST_CASE("Clear")
{
    IntervalSet<int> set(1, 10);
    set.clear();
    CHECK(set.empty());
    CHECK(set.size() == 0);
    CHECK(intervals_of(set) == vector<pair<int, int>>{});

    // clearing an already-empty set is safe
    set.clear();
    CHECK(set.empty());
}

TEST_CASE("Has holes")
{
    IntervalSet<int> set;
    CHECK(! set.has_holes());

    set = IntervalSet<int>(1, 10);
    CHECK(! set.has_holes());

    set.erase(5);
    CHECK(set.has_holes());

    set.erase_less_than(6);
    CHECK(! set.has_holes()); // back to single interval [6,10]
}

TEST_CASE("Size across multiple intervals")
{
    IntervalSet<int> set(1, 10);
    set.erase(3);
    set.erase(7);
    // {[1,2],[4,6],[8,10]} — 2 + 3 + 3 = 8 values
    CHECK(set.size() == 8);
}

TEST_CASE("Contains out-of-range values")
{
    IntervalSet<int> set(5, 10);
    CHECK(! set.contains(4));   // before lower(), hits u > value early exit
    CHECK(! set.contains(11));  // after upper(), falls through loop
}

TEST_CASE("Contains in a gap")
{
    IntervalSet<int> set(1, 10);
    set.erase(5);
    set.erase(6);
    CHECK(! set.contains(5));
    CHECK(! set.contains(6));
    CHECK(set.contains(4));
    CHECK(set.contains(7));
}

TEST_CASE("Erase value not in set")
{
    IntervalSet<int> set(1, 10);
    set.erase(3); // {[1,2],[4,10]}

    set.erase(0);  // before lower() — hits iter->first > value on first interval
    CHECK(intervals_of(set) == vector<pair<int, int>>{{1, 2}, {4, 10}});

    set.erase(3);  // in the gap — hits iter->first > value when reaching [4,10]
    CHECK(intervals_of(set) == vector<pair<int, int>>{{1, 2}, {4, 10}});

    set.erase(11); // after upper() — loop falls through
    CHECK(intervals_of(set) == vector<pair<int, int>>{{1, 2}, {4, 10}});
}

TEST_CASE("Erase single-element interval")
{
    IntervalSet<int> set(5, 5);
    CHECK(set.size() == 1);
    set.erase(5);
    CHECK(set.empty());
    CHECK(intervals_of(set) == vector<pair<int, int>>{});

    // reduce to single-element interval then erase it
    IntervalSet<int> set2(3, 10);
    set2.erase_less_than(7);
    set2.erase_greater_than(7);
    CHECK(intervals_of(set2) == vector<pair<int, int>>{{7, 7}});
    set2.erase(7);
    CHECK(set2.empty());
}

TEST_CASE("Erase less than no-op cases")
{
    IntervalSet<int> set(5, 10);

    set.erase_less_than(4); // below lower() — no change
    CHECK(intervals_of(set) == vector<pair<int, int>>{{5, 10}});

    set.erase_less_than(5); // exactly lower() — no change
    CHECK(intervals_of(set) == vector<pair<int, int>>{{5, 10}});
}

TEST_CASE("Erase less than trims non-first interval")
{
    IntervalSet<int> set(1, 10);
    set.erase(5);
    // {[1,4],[6,10]}

    set.erase_less_than(8); // inside [6,10] — erases [1,4] and trims [6,10] to [8,10]
    CHECK(intervals_of(set) == vector<pair<int, int>>{{8, 10}});
}

TEST_CASE("Erase greater than no-op cases")
{
    IntervalSet<int> set(5, 10);

    set.erase_greater_than(11); // above upper() — loop falls through, no change
    CHECK(intervals_of(set) == vector<pair<int, int>>{{5, 10}});

    set.erase_greater_than(10); // exactly upper() — sets upper to itself, no change
    CHECK(intervals_of(set) == vector<pair<int, int>>{{5, 10}});
}

TEST_CASE("Insert at end single value")
{
    IntervalSet<int> set;

    set.insert_at_end(5); // into empty set
    CHECK(intervals_of(set) == vector<pair<int, int>>{{5, 5}});

    set.insert_at_end(6); // consecutive — extends last interval
    CHECK(intervals_of(set) == vector<pair<int, int>>{{5, 6}});

    set.insert_at_end(8); // gap — starts new interval
    CHECK(intervals_of(set) == vector<pair<int, int>>{{5, 6}, {8, 8}});

    set.insert_at_end(9); // consecutive again
    CHECK(intervals_of(set) == vector<pair<int, int>>{{5, 6}, {8, 9}});
}

TEST_CASE("Insert at end range")
{
    IntervalSet<int> set;

    set.insert_at_end(3, 5); // into empty set
    CHECK(intervals_of(set) == vector<pair<int, int>>{{3, 5}});

    set.insert_at_end(6, 8); // consecutive — merges into last interval
    CHECK(intervals_of(set) == vector<pair<int, int>>{{3, 8}});

    set.insert_at_end(10, 12); // gap — starts new interval
    CHECK(intervals_of(set) == vector<pair<int, int>>{{3, 8}, {10, 12}});
}

TEST_CASE("Each yields values in order")
{
    IntervalSet<int> set(1, 3);
    set.erase(2);
    // {[1,1],[3,3]}

    vector<int> values;
    for (auto v : set.each())
        values.push_back(v);
    CHECK(values == vector<int>{1, 3});
}

TEST_CASE("Each reversed")
{
    IntervalSet<int> set(1, 10);
    set.erase(4);
    set.erase(5);
    // {[1,3],[6,10]}

    vector<int> fwd, rev;
    for (auto v : set.each()) fwd.push_back(v);
    for (auto v : set.each_reversed()) rev.push_back(v);

    auto expected = fwd;
    reverse(expected);
    CHECK(rev == expected);
}

TEST_CASE("Each reversed empty set")
{
    IntervalSet<int> set;
    vector<int> values;
    for (auto v : set.each_reversed())
        values.push_back(v);
    CHECK(values.empty());
}

TEST_CASE("Each gap")
{
    IntervalSet<int> set(1, 10);

    // single interval — no gaps
    vector<int> gaps;
    for (auto v : set.each_gap())
        gaps.push_back(v);
    CHECK(gaps.empty());

    set.erase(3);
    set.erase(4);
    set.erase(8);
    // {[1,2],[5,7],[9,10]} — gaps are 3, 4 and 8
    gaps.clear();
    for (auto v : set.each_gap())
        gaps.push_back(v);
    CHECK(gaps == vector<int>{3, 4, 8});
}

TEST_CASE("Each gap interval")
{
    IntervalSet<int> set(1, 10);

    // single interval — no gap intervals
    vector<pair<int, int>> gap_intervals;
    for (auto v : set.each_gap_interval())
        gap_intervals.push_back(v);
    CHECK(gap_intervals.empty());

    set.erase(3);
    set.erase(4);
    set.erase(8);
    // {[1,2],[5,7],[9,10]}
    // gap intervals are half-open: {3,5} (values 3,4 missing; 5 is start of next)
    //                          and {8,9} (value 8 missing; 9 is start of next)
    gap_intervals.clear();
    for (auto v : set.each_gap_interval())
        gap_intervals.push_back(v);
    CHECK(gap_intervals == vector<pair<int, int>>{{3, 5}, {8, 9}});

    // cross-check: each_gap and each_gap_interval agree on what is missing
    vector<int> from_each_gap, from_gap_intervals;
    for (auto v : set.each_gap())
        from_each_gap.push_back(v);
    for (auto [a, b] : set.each_gap_interval())
        for (int i = a; i != b; ++i)
            from_gap_intervals.push_back(i);
    CHECK(from_each_gap == from_gap_intervals);
}

TEST_CASE("Contains any of with empty sets")
{
    IntervalSet<int> empty;
    IntervalSet<int> nonempty(1, 10);

    CHECK(! empty.contains_any_of(nonempty));
    CHECK(! nonempty.contains_any_of(empty));
    CHECK(! empty.contains_any_of(empty));
}

TEST_CASE("Contains any of with multi-interval sets")
{
    // this = {[1,2],[10,15]}, other = {[3,5],[11,12]}
    // i=[1,2] vs j=[3,5]: no overlap, i ends first → advance i
    // i=[10,15] vs j=[3,5]: no overlap, j ends first → advance j
    // i=[10,15] vs j=[11,12]: overlap → true
    IntervalSet<int> a, b;
    a.insert_at_end(1, 2);
    a.insert_at_end(10, 15);
    b.insert_at_end(3, 5);
    b.insert_at_end(11, 12);
    CHECK(a.contains_any_of(b));
    CHECK(b.contains_any_of(a)); // symmetry

    // two multi-interval sets that are completely disjoint
    // i=[1,3] vs j=[4,6]: no overlap, i ends first → advance i
    // i=[7,9] vs j=[4,6]: no overlap, j ends first → advance j
    // i=[7,9] vs j=[10,12]: no overlap, i ends first → advance i
    // i exhausted → false
    IntervalSet<int> c, d;
    c.insert_at_end(1, 3);
    c.insert_at_end(7, 9);
    d.insert_at_end(4, 6);
    d.insert_at_end(10, 12);
    CHECK(! c.contains_any_of(d));
    CHECK(! d.contains_any_of(c)); // symmetry
}

TEST_CASE("Contains any of overlap at a single point")
{
    // intervals sharing exactly one value
    IntervalSet<int> a(1, 5), b(5, 10);
    CHECK(a.contains_any_of(b));
    CHECK(b.contains_any_of(a));

    // adjacent but not touching: [1,4] and [5,10] share nothing
    IntervalSet<int> c(1, 4), e(5, 10);
    CHECK(! c.contains_any_of(e));
    CHECK(! e.contains_any_of(c));
}

TEST_CASE("Contains any of many advances before overlap")
{
    // build this = {[1,1],[3,3],[5,5],[7,7],[20,30]}
    // build other = {[2,2],[4,4],[6,6],[8,8],[25,25]}
    // the two-pointer walks through four non-overlapping pairs before hitting [20,30] vs [25,25]
    IntervalSet<int> a, b;
    for (int i = 1; i <= 7; i += 2)
        a.insert_at_end(i, i);
    a.insert_at_end(20, 30);
    for (int i = 2; i <= 8; i += 2)
        b.insert_at_end(i, i);
    b.insert_at_end(25, 25);
    CHECK(a.contains_any_of(b));
    CHECK(b.contains_any_of(a));

    // same structure but remove the overlapping tail — should be false
    IntervalSet<int> c, d;
    for (int i = 1; i <= 7; i += 2)
        c.insert_at_end(i, i);
    for (int i = 2; i <= 8; i += 2)
        d.insert_at_end(i, i);
    CHECK(! c.contains_any_of(d));
    CHECK(! d.contains_any_of(c));
}

TEST_CASE("Contains any of brute-force cross-check with multi-interval sets")
{
    // build several multi-interval sets and verify contains_any_of agrees
    // with a direct element-by-element comparison
    auto brute_force = [](const IntervalSet<int> & x, const IntervalSet<int> & y) {
        for (auto v : x.each())
            for (auto w : y.each())
                if (v == w)
                    return true;
        return false;
    };

    IntervalSet<int> s1, s2, s3, s4;
    s1.insert_at_end(1, 3);
    s1.insert_at_end(8, 10);
    s1.insert_at_end(15, 17);

    s2.insert_at_end(4, 7);
    s2.insert_at_end(11, 14);

    s3.insert_at_end(3, 5);
    s3.insert_at_end(9, 11);

    s4.insert_at_end(18, 20);

    for (const auto & a : {s1, s2, s3, s4})
        for (const auto & b : {s1, s2, s3, s4})
            CHECK(a.contains_any_of(b) == brute_force(a, b));
}

namespace
{
    auto intervals_minus(const IntervalSet<int> & a, const IntervalSet<int> & b) -> vector<pair<int, int>>
    {
        vector<pair<int, int>> result;
        for (auto [l, u] : a.each_interval_minus(b))
            result.emplace_back(l, u);
        return result;
    }
}

TEST_CASE("each_interval_minus: empty other yields all of this")
{
    IntervalSet<int> a, b;
    a.insert_at_end(1, 5);
    a.insert_at_end(10, 15);
    CHECK(intervals_minus(a, b) == vector<pair<int, int>>{{1, 5}, {10, 15}});
}

TEST_CASE("each_interval_minus: empty this yields nothing")
{
    IntervalSet<int> a, b(1, 10);
    CHECK(intervals_minus(a, b).empty());
}

TEST_CASE("each_interval_minus: disjoint other yields all of this")
{
    IntervalSet<int> a(1, 5), b(10, 15);
    CHECK(intervals_minus(a, b) == vector<pair<int, int>>{{1, 5}});
    CHECK(intervals_minus(b, a) == vector<pair<int, int>>{{10, 15}});
}

TEST_CASE("each_interval_minus: other entirely covers this yields nothing")
{
    IntervalSet<int> a(3, 5), b(1, 10);
    CHECK(intervals_minus(a, b).empty());
}

TEST_CASE("each_interval_minus: this entirely contains other yields the gaps")
{
    IntervalSet<int> a(1, 10), b(3, 5);
    CHECK(intervals_minus(a, b) == vector<pair<int, int>>{{1, 2}, {6, 10}});
}

TEST_CASE("each_interval_minus: single-value gap")
{
    IntervalSet<int> a(1, 5), b(3, 3);
    CHECK(intervals_minus(a, b) == vector<pair<int, int>>{{1, 2}, {4, 5}});
}

TEST_CASE("each_interval_minus: other touches lower bound")
{
    IntervalSet<int> a(1, 5), b(1, 2);
    CHECK(intervals_minus(a, b) == vector<pair<int, int>>{{3, 5}});
}

TEST_CASE("each_interval_minus: other touches upper bound")
{
    IntervalSet<int> a(1, 5), b(4, 5);
    CHECK(intervals_minus(a, b) == vector<pair<int, int>>{{1, 3}});
}

TEST_CASE("each_interval_minus: other extends beyond this on both sides")
{
    IntervalSet<int> a(3, 7), b(1, 10);
    CHECK(intervals_minus(a, b).empty());
}

TEST_CASE("each_interval_minus: multiple punches in one interval")
{
    IntervalSet<int> a(1, 20);
    IntervalSet<int> b;
    b.insert_at_end(3, 5);
    b.insert_at_end(8, 10);
    b.insert_at_end(15, 17);
    CHECK(intervals_minus(a, b) == vector<pair<int, int>>{{1, 2}, {6, 7}, {11, 14}, {18, 20}});
}

TEST_CASE("each_interval_minus: other spans multiple this-intervals")
{
    IntervalSet<int> a;
    a.insert_at_end(1, 3);
    a.insert_at_end(7, 9);
    a.insert_at_end(13, 15);
    IntervalSet<int> b(2, 14);
    // a = {1..3, 7..9, 13..15}, b = {2..14}
    // a \ b = {1, 15}
    CHECK(intervals_minus(a, b) == vector<pair<int, int>>{{1, 1}, {15, 15}});
}

TEST_CASE("each_interval_minus: a == b yields nothing")
{
    IntervalSet<int> a;
    a.insert_at_end(1, 3);
    a.insert_at_end(8, 10);
    CHECK(intervals_minus(a, a).empty());
}

TEST_CASE("each_interval_minus brute-force cross-check with multi-interval sets")
{
    // For every pair drawn from a small library of multi-interval sets, the
    // generator's yielded intervals must enumerate exactly the values that
    // a brute-force per-value test reports as in `a` and not in `b`.
    auto brute_force = [](const IntervalSet<int> & x, const IntervalSet<int> & y) {
        vector<int> result;
        for (auto v : x.each())
            if (! y.contains(v))
                result.push_back(v);
        return result;
    };

    auto expand = [](const vector<pair<int, int>> & intervals) {
        vector<int> result;
        for (auto [l, u] : intervals)
            for (int v = l; v <= u; ++v)
                result.push_back(v);
        return result;
    };

    IntervalSet<int> s0;
    IntervalSet<int> s1, s2, s3, s4, s5;
    s1.insert_at_end(1, 3);
    s1.insert_at_end(8, 10);
    s1.insert_at_end(15, 17);

    s2.insert_at_end(4, 7);
    s2.insert_at_end(11, 14);

    s3.insert_at_end(3, 5);
    s3.insert_at_end(9, 11);

    s4.insert_at_end(18, 20);

    s5.insert_at_end(1, 20);

    for (const auto & a : {s0, s1, s2, s3, s4, s5})
        for (const auto & b : {s0, s1, s2, s3, s4, s5})
            CHECK(expand(intervals_minus(a, b)) == brute_force(a, b));
}
