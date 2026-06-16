#include <gcs/constraints/table.hh>
#include <gcs/extensional.hh>
#include <gcs/problem.hh>

#include <catch2/catch_test_macros.hpp>

#include <memory>

using namespace gcs;

using std::make_shared;

// Issue #7: Table and NegativeTable take their tuples as an ArrayParam, so a
// caller can hand over a shared_ptr and have the data shared rather than copied
// -- and clone() shares the same buffer too rather than duplicating it. Nothing
// in the tree exercises the shared path, so pin it down here via use_count(): a
// deep copy would leave the original buffer at a use count of one.
TEST_CASE("Table shares tuple storage rather than copying it")
{
    Problem problem;
    auto x = problem.create_integer_variable(0_i, 3_i);
    auto y = problem.create_integer_variable(0_i, 3_i);

    auto tuples = make_shared<const SimpleTuples>(SimpleTuples{{0_i, 1_i}, {2_i, 3_i}});
    REQUIRE(tuples.use_count() == 1);

    Table table{{x, y}, ExtensionalTuples{ArrayParam<SimpleTuples>{tuples}}};
    // The table holds the same buffer, not a deep copy.
    CHECK(tuples.use_count() == 2);

    auto cloned = table.clone();
    // clone() shares the buffer rather than duplicating it.
    CHECK(tuples.use_count() == 3);
}

TEST_CASE("NegativeTable shares tuple storage rather than copying it")
{
    Problem problem;
    auto x = problem.create_integer_variable(0_i, 3_i);
    auto y = problem.create_integer_variable(0_i, 3_i);

    auto tuples = make_shared<const SimpleTuples>(SimpleTuples{{0_i, 1_i}, {2_i, 3_i}});
    REQUIRE(tuples.use_count() == 1);

    NegativeTable table{{x, y}, ExtensionalTuples{ArrayParam<SimpleTuples>{tuples}}};
    CHECK(tuples.use_count() == 2);

    auto cloned = table.clone();
    CHECK(tuples.use_count() == 3);
}
