#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/disjunctive.hh>
#include <gcs/constraints/inverse.hh>
#include <gcs/current_state.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <catch2/catch_test_macros.hpp>

#include <vector>

using namespace gcs;

using std::vector;

TEST_CASE("Problem::create_integer_variable rejects lower > upper")
{
    Problem p;
    REQUIRE_THROWS_AS(p.create_integer_variable(5_i, 3_i), InvalidProblemDefinitionException);
}

TEST_CASE("Problem::create_integer_variable rejects empty domain")
{
    Problem p;
    REQUIRE_THROWS_AS((p.create_integer_variable(vector<Integer>{})), InvalidProblemDefinitionException);
}

TEST_CASE("Cumulative rejects negative capacity")
{
    Problem p;
    auto s = p.create_integer_variable(0_i, 10_i);
    REQUIRE_THROWS_AS((Cumulative{{s}, {1_i}, {1_i}, -1_i}), InvalidProblemDefinitionException);
}

TEST_CASE("Cumulative rejects size mismatch")
{
    Problem p;
    auto s = p.create_integer_variable(0_i, 10_i);
    REQUIRE_THROWS_AS((Cumulative{{s}, {1_i, 2_i}, {1_i}, 5_i}), InvalidProblemDefinitionException);
}

TEST_CASE("Cumulative rejects negative length")
{
    Problem p;
    auto s = p.create_integer_variable(0_i, 10_i);
    REQUIRE_THROWS_AS((Cumulative{{s}, {-1_i}, {1_i}, 5_i}), InvalidProblemDefinitionException);
}

TEST_CASE("Disjunctive rejects size mismatch")
{
    Problem p;
    auto s = p.create_integer_variable(0_i, 10_i);
    REQUIRE_THROWS_AS((Disjunctive{{s}, {1_i, 2_i}}), InvalidProblemDefinitionException);
}

TEST_CASE("Disjunctive rejects negative length")
{
    Problem p;
    auto s = p.create_integer_variable(0_i, 10_i);
    REQUIRE_THROWS_AS((Disjunctive{{s}, {-1_i}}), InvalidProblemDefinitionException);
}

TEST_CASE("Inverse rejects mismatched array sizes")
{
    Problem p;
    auto x1 = p.create_integer_variable(0_i, 1_i);
    auto y1 = p.create_integer_variable(0_i, 1_i);
    auto y2 = p.create_integer_variable(0_i, 1_i);
    p.post(Inverse{{x1}, {y1, y2}});
    REQUIRE_THROWS_AS((solve(p, [](const CurrentState &) -> bool { return true; })),
        InvalidProblemDefinitionException);
}
