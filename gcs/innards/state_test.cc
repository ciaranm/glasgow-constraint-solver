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
    state.for_each_value(var, [&](Integer v) { values.push_back(v); });
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
