#include <gcs/constraints/abs.hh>
#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/in.hh>
#include <gcs/current_state.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/integer.hh>
#include <gcs/problem.hh>
#include <gcs/proof.hh>
#include <gcs/scp_reader.hh>
#include <gcs/solve.hh>

#include <catch2/catch_test_macros.hpp>

#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iterator>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <string_view>

using namespace gcs;

using std::map;
using std::set;
using std::string;
using std::string_view;

namespace
{
    // Read a .scp, enumerate every solution, and return the set of solutions as
    // name -> value maps.
    auto enumerate(string_view scp) -> set<map<string, long long>>
    {
        Problem problem;
        auto variables = read_scp(problem, scp);

        set<map<string, long long>> solutions;
        solve_with(problem,
            SolveCallbacks{.solution = [&](const CurrentState & state) -> bool {
                map<string, long long> solution;
                for (const auto & [name, id] : variables)
                    solution.emplace(name, state(id).raw_value);
                solutions.insert(std::move(solution));
                return true;
            }});
        return solutions;
    }
}

TEST_CASE("read_scp: abs enumerates correctly")
{
    auto solutions = enumerate(R"(
        (
            ( (X -3 3) (Y 0 3) )
            ( (_1 abs X Y) )
        ))");

    CHECK(solutions.size() == 7);
    for (const auto & s : solutions)
        CHECK(s.at("Y") == std::abs(s.at("X")));
}

TEST_CASE("read_scp: all_different enumerates correctly")
{
    auto solutions = enumerate(R"(
        (
            ( (A 0 1) (B 0 1) )
            ( (_1 all_different (A B)) )
        ))");

    CHECK(solutions == set<map<string, long long>>{{{"A", 0}, {"B", 1}}, {{"A", 1}, {"B", 0}}});
}

TEST_CASE("read_scp: in with a mix of integer and variable values")
{
    // V in {0, 3} (constants) or = W (a variable).
    auto solutions = enumerate(R"(
        (
            ( (V 0 5) (W 0 5) )
            ( (_1 in V (0 3 W)) )
        ))");

    for (const auto & s : solutions)
        CHECK((s.at("V") == 0 || s.at("V") == 3 || s.at("V") == s.at("W")));
    // Every (V, W) with V in {0,3} (6 W values each) plus V == W (the rest).
    CHECK(! solutions.empty());
}

TEST_CASE("read_scp: constraint labels and variable names round-trip via the map")
{
    Problem problem;
    auto variables = read_scp(problem, "( ( (X 0 1) (Y 0 1) ) ( (_1 abs X Y) ) )");
    CHECK(variables.size() == 2);
    CHECK(variables.contains("X"));
    CHECK(variables.contains("Y"));
}

namespace
{
    // --prove a problem to `basename`, returning the .scp it wrote.
    auto prove_to_scp(Problem & problem, const std::string & basename) -> std::string
    {
        solve_with(problem, SolveCallbacks{},
            std::make_optional<ProofOptions>(ProofFileNames{basename}, true, false));
        std::ifstream in{basename + ".scp"};
        std::string scp{std::istreambuf_iterator<char>{in}, std::istreambuf_iterator<char>{}};
        for (auto ext : {".opb", ".pbp", ".scp", ".varmap"})
            std::remove((basename + ext).c_str());
        return scp;
    }
}

TEST_CASE("read_scp: a solver-written .scp survives write -> read -> write unchanged")
{
    // Build a problem, write its canonical .scp, read it back, write again, and
    // check the two .scp files are byte-identical -- the round-trip invariant.
    Problem original;
    auto x = original.create_integer_variable(-3_i, 3_i, "X");
    auto y = original.create_integer_variable(0_i, 3_i, "Y");
    auto z = original.create_integer_variable(0_i, 3_i, "Z");
    original.post(Abs{x, y});
    original.post(In{x, std::vector<Integer>{-3_i, -1_i, 1_i, 3_i}});
    original.post(AllDifferent{std::vector<IntegerVariableID>{y, z}});
    auto scp_a = prove_to_scp(original, "scp_reader_roundtrip_a");

    Problem rebuilt;
    read_scp(rebuilt, scp_a);
    auto scp_b = prove_to_scp(rebuilt, "scp_reader_roundtrip_b");

    CHECK(scp_a == scp_b);
    CHECK_FALSE(scp_a.empty());
}

TEST_CASE("read_scp: unsupported and malformed input throws")
{
    CHECK_THROWS_AS(enumerate("( ( (X 0 1) ) ( (_1 frobnicate X) ) )"), ScpReadError);
    CHECK_THROWS_AS(enumerate("( ( (X 0 1) ) )"), ScpReadError);        // not (vars constraints)
    CHECK_THROWS_AS(enumerate("( ( (X 0) ) ( ) )"), ScpReadError);      // bad var decl
    CHECK_THROWS_AS(enumerate("( ( (X zero 1) ) ( ) )"), ScpReadError); // non-integer bound
    CHECK_THROWS_AS(enumerate("not an s-expr ("), innards::SExprParseError);
}
