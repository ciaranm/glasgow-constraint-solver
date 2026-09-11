#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/disjunctive.hh>
#include <gcs/constraints/global_cardinality.hh>
#include <gcs/constraints/inverse.hh>
#include <gcs/current_state.hh>
#include <gcs/exception.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <catch2/catch_test_macros.hpp>

#include <utility>
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

TEST_CASE("GlobalCardinality rejects size mismatch")
{
    // Unchecked, this was a heap-buffer-overflow rather than a diagnosable
    // error: every phase after the constructor indexes _counts by a cover
    // position, and sort_cover_values() ran off the end of the shorter one.
    Problem p;
    auto x = p.create_integer_variable(0_i, 1_i);
    auto c = p.create_integer_variable(0_i, 1_i);
    REQUIRE_THROWS_AS((GlobalCardinality{{x}, {0_i, 1_i}, {c}}), InvalidProblemDefinitionException);
}

TEST_CASE("GlobalCardinality rejects a repeated cover value")
{
    // Both propagators assume the cover is a set: the bounds arm sums the counts
    // over a contiguous slice of the sorted cover, and the GAC arm gives each
    // entry its own value node, so a repeat doubled the demand for one value and
    // lost solutions (#922). Front ends whose input allows a repeat call
    // fold_repeated_cover_values() first.
    Problem p;
    auto x = p.create_integer_variable(0_i, 1_i);
    auto c1 = p.create_integer_variable(0_i, 1_i);
    auto c2 = p.create_integer_variable(0_i, 1_i);
    REQUIRE_THROWS_AS((GlobalCardinality{{x}, {1_i, 1_i}, {c1, c2}}), InvalidProblemDefinitionException);
}

TEST_CASE("fold_repeated_cover_values turns a repeated cover into a distinct one")
{
    Problem p;
    auto c1 = p.create_integer_variable(0_i, 3_i);
    auto c2 = p.create_integer_variable(0_i, 3_i);
    auto c3 = p.create_integer_variable(0_i, 3_i);

    SECTION("a distinct cover is left alone")
    {
        vector<Integer> values{1_i, 2_i};
        vector<IntegerVariableID> counts{c1, c2};
        CHECK(fold_repeated_cover_values(values, counts).empty());
        CHECK(values == vector<Integer>{1_i, 2_i});
        CHECK(counts == vector<IntegerVariableID>{c1, c2});
    }

    SECTION("a repeat keeps the first entry and pairs the later count with it")
    {
        // The kept entry stays where it was, so the cover's order -- which the
        // bounds arm sorts anyway, but the .scp records as posted -- is the
        // input's with the later duplicates struck out.
        vector<Integer> values{1_i, 2_i, 1_i};
        vector<IntegerVariableID> counts{c1, c2, c3};
        auto equalities = fold_repeated_cover_values(values, counts);
        CHECK(equalities == vector<std::pair<IntegerVariableID, IntegerVariableID>>{{c1, c3}});
        CHECK(values == vector<Integer>{1_i, 2_i});
        CHECK(counts == vector<IntegerVariableID>{c1, c2});
    }

    SECTION("repeating the count variable too needs no equality")
    {
        vector<Integer> values{1_i, 1_i};
        vector<IntegerVariableID> counts{c1, c1};
        CHECK(fold_repeated_cover_values(values, counts).empty());
        CHECK(values == vector<Integer>{1_i});
        CHECK(counts == vector<IntegerVariableID>{c1});
    }

    SECTION("three copies of a value pair both later counts with the first")
    {
        vector<Integer> values{1_i, 1_i, 1_i};
        vector<IntegerVariableID> counts{c1, c2, c3};
        auto equalities = fold_repeated_cover_values(values, counts);
        CHECK(equalities == vector<std::pair<IntegerVariableID, IntegerVariableID>>{{c1, c2}, {c1, c3}});
        CHECK(values == vector<Integer>{1_i});
        CHECK(counts == vector<IntegerVariableID>{c1});
    }

    SECTION("a size mismatch is rejected, as the constraint rejects it")
    {
        vector<Integer> values{1_i, 2_i};
        vector<IntegerVariableID> counts{c1};
        CHECK_THROWS_AS(fold_repeated_cover_values(values, counts), InvalidProblemDefinitionException);
    }
}

TEST_CASE("Inverse rejects mismatched array sizes")
{
    Problem p;
    auto x1 = p.create_integer_variable(0_i, 1_i);
    auto y1 = p.create_integer_variable(0_i, 1_i);
    auto y2 = p.create_integer_variable(0_i, 1_i);
    p.post(Inverse{{x1}, {y1, y2}});
    REQUIRE_THROWS_AS((solve(p, [](const CurrentState &) -> bool { return true; })), InvalidProblemDefinitionException);
}
