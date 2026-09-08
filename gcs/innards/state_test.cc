#include <gcs/innards/state.hh>

#include <catch2/catch_test_macros.hpp>

#include <algorithm>
#include <optional>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::count;
using std::make_optional;
using std::pair;
using std::vector;

auto check_range(State & state, IntegerVariableID var, Integer lower, Integer upper) -> void
{
    CHECK(state.bounds(var) == pair{lower, upper});
    CHECK(state.lower_bound(var) == lower);
    CHECK(state.upper_bound(var) == upper);
    for (auto i = -20_i; i <= 20_i; ++i)
        CHECK(state.in_domain(var, i) == (i >= lower && i <= upper));
    vector<Integer> values;
    for (const auto & v : state.each_value_immutable(var))
        values.push_back(v);
    CHECK(Integer(values.size()) == upper - lower + 1_i);
    for (auto i = -20_i; i <= 20_i; ++i)
        CHECK(count(values.begin(), values.end(), i) == (i >= lower && i <= upper ? 1 : 0));
}

TEST_CASE("Variable values")
{
    State state;
    auto var = state.allocate_integer_variable_with_state(1_i, 10_i);

    check_range(state, var, 1_i, 10_i);
    check_range(state, var + 1_i, 2_i, 11_i);
    check_range(state, var - 1_i, 0_i, 9_i);
    check_range(state, -var, -10_i, -1_i);
    check_range(state, -var + 1_i, -9_i, 0_i);
}

TEST_CASE("State infers >=")
{
    State state;
    auto var = state.allocate_integer_variable_with_state(1_i, 10_i);

    SECTION("var >= value")
    {
        CHECK(state.infer(var >= 3_i) == Inference::BoundsChanged);
        check_range(state, var, 3_i, 10_i);
    }

    SECTION("var + offset >= value")
    {
        CHECK(state.infer(var + 1_i >= 5_i) == Inference::BoundsChanged);
        check_range(state, var, 4_i, 10_i);
    }

    SECTION("-var + offset >= value")
    {
        CHECK(state.infer(-var + 1_i >= -7_i) == Inference::BoundsChanged);
        check_range(state, var, 1_i, 8_i);
    }
}

TEST_CASE("State infers <")
{
    State state;
    auto var = state.allocate_integer_variable_with_state(1_i, 10_i);

    SECTION("var < value")
    {
        CHECK(state.infer(var < 7_i) == Inference::BoundsChanged);
        check_range(state, var, 1_i, 6_i);
    }

    SECTION("var + offset < value")
    {
        CHECK(state.infer(var + 1_i < 4_i) == Inference::BoundsChanged);
        check_range(state, var, 1_i, 2_i);
    }

    SECTION("-var + offset < value")
    {
        CHECK(state.infer(-var + 1_i < -2_i) == Inference::BoundsChanged);
        check_range(state, var, 4_i, 10_i);
    }
}

TEST_CASE("State infers !=")
{
    State state;
    auto var = state.allocate_integer_variable_with_state(1_i, 10_i);

    SECTION("var != value")
    {
        CHECK(state.infer(var != 7_i) == Inference::InteriorValuesChanged);
        CHECK(state.bounds(var) == pair{1_i, 10_i});
        for (auto i = 1_i; i <= 10_i; ++i)
            CHECK(state.in_domain(var, i) == (i != 7_i));
    }

    SECTION("var + offset != value")
    {
        CHECK(state.infer(var + 1_i != 7_i) == Inference::InteriorValuesChanged);
        CHECK(state.bounds(var) == pair{1_i, 10_i});
        for (auto i = 1_i; i <= 10_i; ++i)
            CHECK(state.in_domain(var, i) == (i != 6_i));
    }

    SECTION("-var + offset != value")
    {
        CHECK(state.infer(-var + 1_i != -7_i) == Inference::InteriorValuesChanged);
        CHECK(state.bounds(var) == pair{1_i, 10_i});
        for (auto i = 1_i; i <= 10_i; ++i)
            CHECK(state.in_domain(var, i) == (i != 8_i));
    }
}

TEST_CASE("State infers =")
{
    State state;
    auto var = state.allocate_integer_variable_with_state(1_i, 10_i);

    SECTION("var = value")
    {
        CHECK(state.infer(var == 7_i) == Inference::Instantiated);
        check_range(state, var, 7_i, 7_i);
        CHECK(state.optional_single_value(var) == make_optional(7_i));
    }

    SECTION("var + offset = value")
    {
        CHECK(state.infer(var + 1_i == 7_i) == Inference::Instantiated);
        check_range(state, var, 6_i, 6_i);
        CHECK(state.optional_single_value(var) == make_optional(6_i));
    }

    SECTION("-var + offset = value")
    {
        CHECK(state.infer(-var + 1_i == -7_i) == Inference::Instantiated);
        check_range(state, var, 8_i, 8_i);
        CHECK(state.optional_single_value(var) == make_optional(8_i));
    }
}

TEST_CASE("domains_intersect / domain_intersects_with handle views")
{
    State state;
    auto a = state.allocate_integer_variable_with_state(1_i, 5_i);
    auto b = state.allocate_integer_variable_with_state(3_i, 7_i);
    auto c = state.allocate_integer_variable_with_state(8_i, 10_i);

    SECTION("two simple variables, overlap and disjoint")
    {
        CHECK(state.domains_intersect(a, b));       // {1..5} vs {3..7}
        CHECK_FALSE(state.domains_intersect(a, c)); // {1..5} vs {8..10}
    }

    SECTION("simple variable vs constant")
    {
        CHECK(state.domains_intersect(a, constant_variable(3_i)));
        CHECK_FALSE(state.domains_intersect(a, constant_variable(0_i)));
    }

    SECTION("offset views")
    {
        // a in {1..5}; a + 5 in {6..10}; overlap with c={8..10} on {8..10}.
        CHECK(state.domains_intersect(a + 5_i, c));
        // a + 10 in {11..15}; disjoint from c.
        CHECK_FALSE(state.domains_intersect(a + 10_i, c));
    }

    SECTION("negated view vs simple variable")
    {
        // -a in {-5..-1}; b in {3..7}; disjoint.
        CHECK_FALSE(state.domains_intersect(-a, b));
        // -a in {-5..-1}; -b in {-7..-3}; overlap on {-5..-3}.
        CHECK(state.domains_intersect(-a, -b));
    }

    SECTION("negated view with offset")
    {
        // -a + 8 in {3..7} (since a in {1..5}); overlaps with b.
        CHECK(state.domains_intersect(-a + 8_i, b));
        // -a + 8 in {3..7}; disjoint from c={8..10}.
        CHECK_FALSE(state.domains_intersect(-a + 8_i, c));
    }

    SECTION("domain_intersects_with(view, set)")
    {
        IntervalSet<Integer> set;
        set.insert_at_end(-3_i, -1_i);
        // -a in {-5..-1}; intersects {-3..-1}.
        CHECK(state.domain_intersects_with(-a, set));

        IntervalSet<Integer> disjoint;
        disjoint.insert_at_end(20_i, 30_i);
        CHECK_FALSE(state.domain_intersects_with(-a, disjoint));
    }
}

TEST_CASE("domain_is_subset_of handles views, holes and constants")
{
    State state;
    auto a = state.allocate_integer_variable_with_state(1_i, 5_i);
    auto holey = state.allocate_integer_variable_with_state(1_i, 10_i);
    // holey is now {1..3, 5..6, 8..10}.
    (void)state.infer(holey != 4_i);
    (void)state.infer(holey != 7_i);

    auto set_of = [](std::initializer_list<std::pair<Integer, Integer>> ivs) {
        IntervalSet<Integer> r;
        for (const auto & [l, u] : ivs)
            r.insert_at_end(l, u);
        return r;
    };

    SECTION("simple variable, no offset --- the no-copy path")
    {
        CHECK(state.domain_is_subset_of(a, set_of({{1_i, 5_i}})));
        CHECK(state.domain_is_subset_of(a, set_of({{0_i, 9_i}})));
        CHECK_FALSE(state.domain_is_subset_of(a, set_of({{2_i, 5_i}})));
        CHECK_FALSE(state.domain_is_subset_of(a, set_of({{1_i, 4_i}})));
        // A set covering both ends but not the middle: the case a bounds-only
        // test would get wrong.
        CHECK_FALSE(state.domain_is_subset_of(a, set_of({{1_i, 2_i}, {4_i, 5_i}})));
    }

    SECTION("a domain with holes needs only the values it still has")
    {
        CHECK(state.domain_is_subset_of(holey, set_of({{1_i, 3_i}, {5_i, 6_i}, {8_i, 10_i}})));
        // The holes themselves need not be covered.
        CHECK_FALSE(state.domain_is_subset_of(holey, set_of({{1_i, 6_i}})));
        CHECK(state.domain_is_subset_of(holey, set_of({{1_i, 10_i}})));
    }

    SECTION("offset view")
    {
        // a + 5 in {6..10}.
        CHECK(state.domain_is_subset_of(a + 5_i, set_of({{6_i, 10_i}})));
        CHECK_FALSE(state.domain_is_subset_of(a + 5_i, set_of({{1_i, 5_i}})));
    }

    SECTION("negated view, including one with holes")
    {
        // -a in {-5..-1}.
        CHECK(state.domain_is_subset_of(-a, set_of({{-5_i, -1_i}})));
        CHECK_FALSE(state.domain_is_subset_of(-a, set_of({{-4_i, -1_i}})));
        // -holey in {-10..-8, -6..-5, -3..-1}.
        CHECK(state.domain_is_subset_of(-holey, set_of({{-10_i, -8_i}, {-6_i, -5_i}, {-3_i, -1_i}})));
        CHECK_FALSE(state.domain_is_subset_of(-holey, set_of({{-10_i, -5_i}})));
    }

    SECTION("negated view with offset")
    {
        // -a + 8 in {3..7}.
        CHECK(state.domain_is_subset_of(-a + 8_i, set_of({{3_i, 7_i}})));
        CHECK_FALSE(state.domain_is_subset_of(-a + 8_i, set_of({{4_i, 7_i}})));
    }

    SECTION("constant")
    {
        CHECK(state.domain_is_subset_of(constant_variable(3_i), set_of({{1_i, 5_i}})));
        CHECK_FALSE(state.domain_is_subset_of(constant_variable(9_i), set_of({{1_i, 5_i}})));
    }

    SECTION("agrees with the per-value meaning it replaces")
    {
        for (Integer lo = 0_i; lo <= 11_i; ++lo)
            for (Integer hi = lo; hi <= 11_i; ++hi) {
                auto set = set_of({{lo, hi}});
                bool all = true;
                for (const auto & v : state.each_value_immutable(holey))
                    if (! set.contains(v))
                        all = false;
                CHECK(state.domain_is_subset_of(holey, set) == all);
            }
    }
}

TEST_CASE("copy_of_values / domains_intersect on multi-interval negated views")
{
    State state;
    auto a = state.allocate_integer_variable_with_state(1_i, 10_i);
    // Punch holes: a's domain is now {1..3, 5..6, 8..10}.
    (void)state.infer(a != 4_i);
    (void)state.infer(a != 7_i);

    SECTION("copy_of_values on a multi-interval negated view")
    {
        auto values = state.copy_of_values(-a);
        // -a's values are {-10..-8, -6..-5, -3..-1} (negation reverses
        // the interval order).
        vector<pair<Integer, Integer>> intervals;
        for (auto p : values.each_interval())
            intervals.push_back(p);
        CHECK(intervals == vector<pair<Integer, Integer>>{{-10_i, -8_i}, {-6_i, -5_i}, {-3_i, -1_i}});
    }

    SECTION("copy_of_values on a multi-interval negated view with offset")
    {
        auto values = state.copy_of_values(-a + 7_i);
        // (-a + 7)'s values are -10+7=-3, -8+7=-1; -6+7=1, -5+7=2;
        // -3+7=4, -1+7=6 -> {-3..-1, 1..2, 4..6}.
        vector<pair<Integer, Integer>> intervals;
        for (auto p : values.each_interval())
            intervals.push_back(p);
        CHECK(intervals == vector<pair<Integer, Integer>>{{-3_i, -1_i}, {1_i, 2_i}, {4_i, 6_i}});
    }

    SECTION("domains_intersect: both sides negated views with offsets, multi-interval")
    {
        auto b = state.allocate_integer_variable_with_state(0_i, 5_i);
        (void)state.infer(b != 2_i);
        // b in {0..1, 3..5}; -b in {-5..-3, -1..0}; -b + 4 in {-1..1, 3..4}.
        // -a + 7 in {-3..-1, 1..2, 4..6} (computed above).
        // The two share -1, 1, and 4 -> non-empty intersection.
        CHECK(state.domains_intersect(-a + 7_i, -b + 4_i));
    }

    SECTION("domains_intersect: both negated, disjoint")
    {
        auto c = state.allocate_integer_variable_with_state(20_i, 30_i);
        // -a in {-10..-8, -6..-5, -3..-1}; -c in {-30..-20}; disjoint.
        CHECK_FALSE(state.domains_intersect(-a, -c));
    }

    SECTION("domains_intersect with negated view passed in either argument position")
    {
        auto d = state.allocate_integer_variable_with_state(-2_i, 0_i);
        // d in {-2..0}; -a in {-10..-8, -6..-5, -3..-1}.
        // d ∩ -a = {-2..-1}, non-empty.
        CHECK(state.domains_intersect(-a, d));
        CHECK(state.domains_intersect(d, -a)); // symmetry
    }
}

TEST_CASE("Every way of iterating a domain hands values out in ascending order")
{
    // Issue #890: the each_value family applied a view to the underlying domain
    // in stored order, and negation reverses that, so a negated view's values
    // came out descending --- where copy_of_values() and each_value_reversed()
    // sorted them. The four entry points and copy_of_values() have to agree,
    // and ascending has to mean ascending in the *variable's own* values.
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 9_i);
    for (auto h : {2_i, 3_i, 6_i})
        REQUIRE(Inference::Contradiction != state.infer_not_equal(x, h));
    // x is now {0, 1, 4, 5, 7, 8, 9}: holes, so a single-interval walk would not
    // catch a reversal, and an even count, so a symmetric one would not either.

    auto ascending = [](const vector<Integer> & vs) {
        return std::is_sorted(vs.begin(), vs.end()) && std::adjacent_find(vs.begin(), vs.end()) == vs.end();
    };

    for (auto var : {IntegerVariableID{x}, IntegerVariableID{x + 100_i}, IntegerVariableID{-x}, IntegerVariableID{-x + 20_i}}) {
        // Bound to a local rather than iterated off the temporary:
        // IntervalSet::each() borrows the set it is called on, and only
        // P2718R0's extended lifetime for range-init temporaries makes
        // `copy_of_values(var).each()` safe --- so on a compiler without it, the
        // set is gone before the first value is read. GCC 15 has it and GCC 14
        // does not, which is a difference between two of the CI lanes.
        auto values = state.copy_of_values(var);
        vector<Integer> from_copy;
        for (auto v : values.each())
            from_copy.push_back(v);

        vector<Integer> immutable, mutable_, for_immutable, for_mutable;
        for (auto v : state.each_value_immutable(var))
            immutable.push_back(v);
        for (auto v : state.each_value_mutable(var))
            mutable_.push_back(v);
        state.for_each_value_immutable(var, [&](Integer v) { for_immutable.push_back(v); });
        state.for_each_value_mutable(var, [&](Integer v) { for_mutable.push_back(v); });

        CHECK(ascending(from_copy));
        CHECK(immutable == from_copy);
        CHECK(mutable_ == from_copy);
        CHECK(for_immutable == from_copy);
        CHECK(for_mutable == from_copy);

        // And the reversed generator really is the other direction, rather than
        // accidentally agreeing with a walk that was already backwards.
        vector<Integer> reversed;
        for (auto v : values.each_reversed())
            reversed.push_back(v);
        auto flipped = from_copy;
        std::reverse(flipped.begin(), flipped.end());
        CHECK(reversed == flipped);
    }

    // A constant is a one-value domain whichever way it is asked for.
    vector<Integer> constant;
    for (auto v : state.each_value_immutable(ConstantIntegerVariableID{7_i}))
        constant.push_back(v);
    CHECK(constant == vector<Integer>{7_i});
}

TEST_CASE("Early exit from a domain walk stops at the smallest values, views included")
{
    // The other half of ascending: for_each_value_*'s early exit has to give up
    // the *first* values in the variable's own order, or a caller that stops
    // after k of them gets the wrong k for a negated view.
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 5_i);
    auto var = IntegerVariableID{-x + 10_i}; // 5..10

    vector<Integer> first_three;
    state.for_each_value_immutable(var, [&](Integer v) {
        first_three.push_back(v);
        return first_three.size() < 3;
    });
    CHECK(first_three == vector<Integer>{5_i, 6_i, 7_i});
}
