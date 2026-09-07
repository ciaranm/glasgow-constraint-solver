#include <gcs/problem.hh>

#include <catch2/catch_test_macros.hpp>

#include <string>
#include <vector>

using namespace gcs;
using namespace std::string_literals;

// For now, these are an indirect way of testing the name-checking code in (private) Problem::check_name

TEST_CASE("Problem accepts valid variable names")
{
    Problem p;

    CHECK_NOTHROW(p.create_integer_variable(0_i, 1_i, "x"s));
    CHECK_NOTHROW(p.create_integer_variable(0_i, 1_i, "_x"s));
    CHECK_NOTHROW(p.create_integer_variable(0_i, 1_i, "x_1"s));
    CHECK_NOTHROW(p.create_integer_variable(0_i, 1_i, "x[0]"s));
    CHECK_NOTHROW(p.create_integer_variable(0_i, 1_i, "x[0][1]"s));
    CHECK_NOTHROW(p.create_integer_variable(0_i, 1_i, "x[0]{y}[1]"s));
    CHECK_NOTHROW(p.create_integer_variable(0_i, 1_i, "x[0]{y[1]}"s));
    CHECK_NOTHROW(p.create_integer_variable(0_i, 1_i, "x[y[0{1}]]"s));
    CHECK_NOTHROW(p.create_integer_variable(0_i, 1_i, "x{row}"s));
}

TEST_CASE("Problem rejects illegal variable names")
{
    Problem p;

    CHECK_THROWS_AS(p.create_integer_variable(0_i, 1_i, ""s), NamingError);
    CHECK_THROWS_AS(p.create_integer_variable(0_i, 1_i, "1x"s), NamingError);
    CHECK_THROWS_AS(p.create_integer_variable(0_i, 1_i, "x y"s), NamingError);
    CHECK_THROWS_AS(p.create_integer_variable(0_i, 1_i, "x()"s), NamingError);
}

TEST_CASE("Problem rejects unbalanced or mismatched brackets")
{
    Problem p;

    CHECK_THROWS_AS(p.create_integer_variable(0_i, 1_i, "x["s), NamingError);
    CHECK_THROWS_AS(p.create_integer_variable(0_i, 1_i, "x}"s), NamingError);
    CHECK_THROWS_AS(p.create_integer_variable(0_i, 1_i, "x[}"s), NamingError);
    CHECK_THROWS_AS(p.create_integer_variable(0_i, 1_i, "x{]"s), NamingError);
}

TEST_CASE("Problem rejects duplicate variable names")
{
    Problem p;

    CHECK_NOTHROW(p.create_integer_variable(0_i, 1_i, "dup"s));
    CHECK_THROWS_AS(p.create_integer_variable(0_i, 1_i, "dup"s), NamingError);
}

TEST_CASE("Problem rejects a domain too wide for the proof model")
{
    // The boundary is measured rather than chosen: at these bounds LessThan,
    // Plus and AllDifferent all write their model, and one bit wider all three
    // abort part-way through emission and leave a truncated OPB (issue #852).
    Problem p;
    CHECK_NOTHROW(p.create_integer_variable(Integer::min_bounded_value(), Integer::max_bounded_value()));
    CHECK_THROWS_AS(p.create_integer_variable(Integer::min_bounded_value() - 1_i, 0_i), InvalidProblemDefinitionException);
    CHECK_THROWS_AS(p.create_integer_variable(0_i, Integer::max_bounded_value() + 1_i), InvalidProblemDefinitionException);
    CHECK_THROWS_AS(p.create_integer_variable(Integer::min_value() / 2_i, Integer::max_value() / 2_i), InvalidProblemDefinitionException);

    // The vector overload goes through the same check.
    CHECK_THROWS_AS(p.create_integer_variable(std::vector<Integer>{0_i, Integer::max_value() / 2_i}), InvalidProblemDefinitionException);
}
