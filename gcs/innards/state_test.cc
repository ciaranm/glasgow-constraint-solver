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
