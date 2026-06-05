#include <gcs/innards/s_expr.hh>

#include <catch2/catch_test_macros.hpp>

#include <string>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
using std::format;
#else
#include <fmt/format.h>
using fmt::format;
#endif

using namespace gcs;
using namespace gcs::innards;

using std::string;
using std::vector;

TEST_CASE("SExpr: an atom round-trips")
{
    auto e = parse_s_expr("_1");
    CHECK(e.is_atom());
    CHECK(e.as_atom() == "_1");
    CHECK(format("{}", e) == "_1");
}

TEST_CASE("SExpr: a flat list round-trips canonically")
{
    auto e = parse_s_expr("(_1 abs _2 _3)");
    REQUIRE(e.is_list());
    REQUIRE(e.as_list().size() == 4);
    CHECK(e.as_list()[0].as_atom() == "_1");
    CHECK(e.as_list()[1].as_atom() == "abs");
    CHECK(format("{}", e) == "(_1 abs _2 _3)");
}

TEST_CASE("SExpr: incidental whitespace is normalised away")
{
    // Leading/trailing/inner spacing, tabs and newlines all collapse to the
    // single canonical form: this is exactly the messy hand-formatting the
    // old string-built s_exprify produced (e.g. "( 0 3)").
    CHECK(format("{}", parse_s_expr("(   0    3 )")) == "(0 3)");
    CHECK(format("{}", parse_s_expr("  (_1   all_different ( _1 _1 _2 _2))  ")) ==
        "(_1 all_different (_1 _1 _2 _2))");
    CHECK(format("{}", parse_s_expr("(a\n\tb\r\n c)")) == "(a b c)");
}

TEST_CASE("SExpr: nested lists round-trip")
{
    auto s = "((_4 _5) (_6 _7))";
    auto e = parse_s_expr(s);
    REQUIRE(e.is_list());
    REQUIRE(e.as_list().size() == 2);
    CHECK(e.as_list()[0].is_list());
    CHECK(format("{}", e) == s);
}

TEST_CASE("SExpr: the empty list")
{
    auto e = parse_s_expr("()");
    REQUIRE(e.is_list());
    CHECK(e.as_list().empty());
    CHECK(format("{}", e) == "()");
    CHECK(format("{}", parse_s_expr("(  )")) == "()");
}

TEST_CASE("SExpr: a view parses as a list and re-renders identically")
{
    // s_expr_name_of renders a ViewOfIntegerVariableID as "(-_1 + 17)" /
    // "(_2 + 0)"; that textual form already is canonical s-expr spacing, so a
    // constraint line embedding a view round-trips exactly.
    CHECK(format("{}", parse_s_expr("(-_1 + 17)")) == "(-_1 + 17)");
    CHECK(format("{}", parse_s_expr("(_2 + 0)")) == "(_2 + 0)");
    CHECK(format("{}", parse_s_expr("(_1 abs (-_1 + 17) _2)")) == "(_1 abs (-_1 + 17) _2)");
}

TEST_CASE("SExpr: reification-condition triples, signs, symbols and commas are atoms-in-lists")
{
    CHECK(format("{}", parse_s_expr("(_2 neq 1)")) == "(_2 neq 1)");
    CHECK(parse_s_expr("-3").as_atom() == "-3");
    CHECK(parse_s_expr(">=").as_atom() == ">=");
    CHECK(parse_s_expr("*").as_atom() == "*");
    // The element index form "_4,0" is a single atom (the comma is an ordinary
    // atom character). NOTE: this comma form is suspect and likely to change.
    CHECK(parse_s_expr("_4,0").as_atom() == "_4,0");
}

TEST_CASE("SExpr: the canonical forms the refactored constraints now emit")
{
    for (auto s : {
             "(_1 abs _2 _3)",
             "(_3 all_different (_1 _1 _2 _2))",
             "(_1 less_equal _2 _3)",
             "(_1 less_equal_iff (_2 != 1) _3 _4)",
             "(_5 in _2 (0 1 _3))"}) {
        CHECK(format("{}", parse_s_expr(s)) == s);
    }
}

TEST_CASE("SExpr: parsing is idempotent under print-then-reparse")
{
    for (auto s : {"x", "()", "(a (b c) ((d)) e)", "(  messy   ( spacing ) )", "(-_1 + 17)"}) {
        auto once = parse_s_expr(s);
        auto twice = parse_s_expr(format("{}", once));
        CHECK(once == twice);
        CHECK(format("{}", once) == format("{}", twice));
    }
}

TEST_CASE("SExpr: structural equality ignores formatting but respects shape")
{
    CHECK(parse_s_expr("( a b )") == parse_s_expr("(a   b)"));
    CHECK_FALSE(parse_s_expr("(a b)") == parse_s_expr("(a (b))"));
    CHECK_FALSE(parse_s_expr("a") == parse_s_expr("(a)"));
}

TEST_CASE("SExpr: a sequence of top-level terms")
{
    auto seq = parse_s_expr_seq("(a b)  c\n(d)");
    REQUIRE(seq.size() == 3);
    CHECK(seq[0].is_list());
    CHECK(seq[1].as_atom() == "c");
    CHECK(seq[2].is_list());
    CHECK(parse_s_expr_seq("   ").empty());
}

TEST_CASE("SExpr: the '#' alternate form drops a list's enclosing parentheses")
{
    // This is the shape Constraint::s_exprify returns; solve() wraps it in ().
    auto body = SExpr::list({SExpr::atom("_1"),
        SExpr::atom("abs"),
        parse_s_expr("_2"),
        parse_s_expr("(-_1 + 17)")});
    CHECK(format("{:#}", body) == "_1 abs _2 (-_1 + 17)");
    CHECK(format("{}", body) == "(_1 abs _2 (-_1 + 17))");
    // Only the outermost list loses its parentheses; nested lists keep theirs.
    CHECK(format("{:#}", parse_s_expr("(a (b c) d)")) == "a (b c) d");
    CHECK(format("{:#}", SExpr::list({})) == "");
}

TEST_CASE("SExpr: malformed input throws")
{
    CHECK_THROWS_AS(parse_s_expr(""), SExprParseError);
    CHECK_THROWS_AS(parse_s_expr("   "), SExprParseError);
    CHECK_THROWS_AS(parse_s_expr("(a b"), SExprParseError); // unclosed
    CHECK_THROWS_AS(parse_s_expr("a)"), SExprParseError);   // stray close
    CHECK_THROWS_AS(parse_s_expr(")"), SExprParseError);
    CHECK_THROWS_AS(parse_s_expr("a b"), SExprParseError); // two top-level terms
}

TEST_CASE("SExpr: as_atom / as_list on the wrong kind throws")
{
    CHECK_THROWS_AS(parse_s_expr("(a)").as_atom(), SExprParseError);
    CHECK_THROWS_AS(parse_s_expr("a").as_list(), SExprParseError);
}
