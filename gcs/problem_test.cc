#include <gcs/problem.hh>

#include <catch2/catch_test_macros.hpp>

#include <string>

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
