#include <gcs/constraints/abs.hh>
#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/all_equal.hh>
#include <gcs/constraints/among/among.hh>
#include <gcs/constraints/at_most_one/at_most_one.hh>
#include <gcs/constraints/bin_packing.hh>
#include <gcs/constraints/circuit.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/count.hh>
#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/difference/difference_constraints.hh>
#include <gcs/constraints/disjunctive.hh>
#include <gcs/constraints/disjunctive_2d.hh>
#include <gcs/constraints/divide.hh>
#include <gcs/constraints/element.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/global_cardinality.hh>
#include <gcs/constraints/in.hh>
#include <gcs/constraints/increasing.hh>
#include <gcs/constraints/knapsack/knapsack.hh>
#include <gcs/constraints/lex.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/constraints/logical.hh>
#include <gcs/constraints/mdd.hh>
#include <gcs/constraints/min_distance.hh>
#include <gcs/constraints/min_max.hh>
#include <gcs/constraints/modulus.hh>
#include <gcs/constraints/multiply.hh>
#include <gcs/constraints/nogoods/nogoods.hh>
#include <gcs/constraints/parity.hh>
#include <gcs/constraints/power.hh>
#include <gcs/constraints/reachable/reachable.hh>
#include <gcs/constraints/regular/regular.hh>
#include <gcs/constraints/regular/regular_bacchus.hh>
#include <gcs/constraints/regular/regular_legacy.hh>
#include <gcs/constraints/seq_precede_chain/seq_precede_chain.hh>
#include <gcs/constraints/smart_table/smart_table.hh>
#include <gcs/constraints/table/negative_table.hh>
#include <gcs/constraints/table/table.hh>
#include <gcs/constraints/value_precede/value_precede.hh>
#include <gcs/current_state.hh>
#include <gcs/expression.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/integer.hh>
#include <gcs/problem.hh>
#include <gcs/proof.hh>
#include <gcs/scp_reader.hh>
#include <gcs/solve.hh>

#include <catch2/catch_test_macros.hpp>

#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iterator>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

using namespace gcs;

using std::map;
using std::set;
using std::string;
using std::string_view;
using std::vector;

namespace
{
    // Read a .scp, enumerate every solution, and return the set of solutions as
    // name -> value maps.
    auto enumerate(string_view scp) -> set<map<string, long long>>
    {
        Problem problem;
        auto variables = read_scp(problem, scp).variables;

        set<map<string, long long>> solutions;
        solve_with(problem, //
            SolveCallbacks{ //
                .solution = [&](const CurrentState & state) -> bool {
                    map<string, long long> solution;
                    for (const auto & [name, id] : variables)
                        solution.emplace(name, state(id).raw_value);
                    solutions.insert(std::move(solution));
                    return true;
                }});
        return solutions;
    }

    // --prove a problem to `basename`, returning the .scp it wrote.
    auto prove_to_scp(Problem & problem, const std::string & basename) -> std::string
    {
        solve_with(problem, SolveCallbacks{}, std::make_optional<ProofOptions>(ProofFileNames{basename}));
        std::ifstream in{basename + ".scp"};
        std::string scp{std::istreambuf_iterator<char>{in}, std::istreambuf_iterator<char>{}};
        for (auto ext : {".opb", ".pbp", ".scp", ".varmap"})
            std::remove((basename + ext).c_str());
        return scp;
    }
}

TEST_CASE("read_scp: abs enumerates correctly")
{
    auto solutions = enumerate(R"(
        (
            (version 1)
            (variables (X -3 3) (Y 0 3))
            (constraints (_1 abs X Y))
            (prob_type enumerate)
        ))");

    CHECK(solutions.size() == 7);
    for (const auto & s : solutions)
        CHECK(s.at("Y") == std::abs(s.at("X")));
}

TEST_CASE("read_scp: all_different enumerates correctly")
{
    auto solutions = enumerate(R"(
        (
            (version 1)
            (variables (A 0 1) (B 0 1))
            (constraints (_1 all_different (A B)))
            (prob_type enumerate)
        ))");

    CHECK(solutions == set<map<string, long long>>{{{"A", 0}, {"B", 1}}, {{"A", 1}, {"B", 0}}});
}

TEST_CASE("read_scp: all_equal enumerates correctly")
{
    auto solutions = enumerate(R"(
        (
            (version 1)
            (variables (A 0 2) (B 0 2) (C 0 2))
            (constraints (_1 all_equal (A B C)))
            (prob_type enumerate)
        ))");

    CHECK(solutions == set<map<string, long long>>{{{"A", 0}, {"B", 0}, {"C", 0}}, {{"A", 1}, {"B", 1}, {"C", 1}}, {{"A", 2}, {"B", 2}, {"C", 2}}});
}

TEST_CASE("read_scp: the increasing family enumerates correctly")
{
    for (const auto & s :
        enumerate("( (version 1) (variables (X 0 2) (Y 0 2) (Z 0 2)) (constraints (_1 increasing (X Y Z))) (prob_type enumerate) )"))
        CHECK((s.at("X") <= s.at("Y") && s.at("Y") <= s.at("Z")));
    for (const auto & s :
        enumerate("( (version 1) (variables (X 0 3) (Y 0 3) (Z 0 3)) (constraints (_1 strictly_increasing (X Y Z))) (prob_type enumerate) )"))
        CHECK((s.at("X") < s.at("Y") && s.at("Y") < s.at("Z")));
    for (const auto & s :
        enumerate("( (version 1) (variables (X 0 2) (Y 0 2) (Z 0 2)) (constraints (_1 decreasing (X Y Z))) (prob_type enumerate) )"))
        CHECK((s.at("X") >= s.at("Y") && s.at("Y") >= s.at("Z")));
    for (const auto & s :
        enumerate("( (version 1) (variables (X 0 3) (Y 0 3) (Z 0 3)) (constraints (_1 strictly_decreasing (X Y Z))) (prob_type enumerate) )"))
        CHECK((s.at("X") > s.at("Y") && s.at("Y") > s.at("Z")));
}

TEST_CASE("read_scp: circuit enumerates the Hamiltonian cycles")
{
    // Successor of each of three nodes; the only single cycles are the two
    // directed 3-cycles.
    auto solutions = enumerate(R"(
        (
            (version 1)
            (variables (A 0 2) (B 0 2) (C 0 2))
            (constraints (_1 circuit (A B C)))
            (prob_type enumerate)
        ))");

    CHECK(solutions == set<map<string, long long>>{{{"A", 1}, {"B", 2}, {"C", 0}}, {{"A", 2}, {"B", 0}, {"C", 1}}});
}

TEST_CASE("read_scp: array_min / array_max enumerate correctly")
{
    for (const auto & s :
        enumerate("( (version 1) (variables (X 0 2) (Y 0 2) (Z 0 2) (R 0 2)) (constraints (_1 array_min (X Y Z) R)) (prob_type enumerate) )"))
        CHECK(s.at("R") == std::min({s.at("X"), s.at("Y"), s.at("Z")}));
    for (const auto & s :
        enumerate("( (version 1) (variables (X 0 2) (Y 0 2) (Z 0 2) (R 0 2)) (constraints (_1 array_max (X Y Z) R)) (prob_type enumerate) )"))
        CHECK(s.at("R") == std::max({s.at("X"), s.at("Y"), s.at("Z")}));
}

TEST_CASE("read_scp: logical and / or reification-tuple forms enumerate correctly")
{
    // Y >= 1  <->  (B1 >= 1) and (B2 >= 1)
    for (const auto & s : enumerate(
             "( (version 1) (variables (B1 0 1) (B2 0 1) (Y 0 1)) (constraints (_1 and ((B1 >= 1) (B2 >= 1)) (Y >= 1))) (prob_type enumerate) )"))
        CHECK((s.at("Y") == 1) == (s.at("B1") == 1 && s.at("B2") == 1));
    // Y >= 1  <->  (B1 >= 1) or (B2 >= 1)
    for (const auto & s :
        enumerate("( (version 1) (variables (B1 0 1) (B2 0 1) (Y 0 1)) (constraints (_1 or ((B1 >= 1) (B2 >= 1)) (Y >= 1))) (prob_type enumerate) )"))
        CHECK((s.at("Y") == 1) == (s.at("B1") == 1 || s.at("B2") == 1));
    // bool_clause-style negated operands: D >= 1  <->  (A = 0) or (B = 0)
    for (const auto & s :
        enumerate("( (version 1) (variables (A 0 1) (B 0 1) (D 0 1)) (constraints (_1 or ((A = 0) (B = 0)) (D >= 1))) (prob_type enumerate) )"))
        CHECK((s.at("D") == 1) == (s.at("A") == 0 || s.at("B") == 0));
}

TEST_CASE("read_scp: parity reification-tuple form enumerates correctly")
{
    // An odd number of (A >= 1), (B >= 1), (C >= 1) hold; the output tuple
    // (1 >= 1) is statically true (bare odd parity).
    for (const auto & s : enumerate("( (version 1) (variables (A 0 1) (B 0 1) (C 0 1)) (constraints (_1 parity ((A >= 1) (B >= 1) (C >= 1)) (1 >= "
                                    "1))) (prob_type enumerate) )"))
        CHECK((s.at("A") + s.at("B") + s.at("C")) % 2 == 1);
    // A non-static output tuple is rejected: only bare odd parity is supported.
    CHECK_THROWS_AS(
        enumerate("( (version 1) (variables (A 0 1) (B 0 1) (Y 0 1)) (constraints (_1 parity ((A >= 1) (B >= 1)) (Y >= 1))) (prob_type enumerate) )"),
        ScpReadError);
}

TEST_CASE("read_scp: lex comparisons enumerate correctly")
{
    // (A B) >lex (C D): A > C, or A == C and B > D.
    for (const auto & s : enumerate(
             "( (version 1) (variables (A 0 2) (B 0 2) (C 0 2) (D 0 2)) (constraints (_1 lex_greater_than (A B) (C D))) (prob_type enumerate) )"))
        CHECK(((s.at("A") > s.at("C")) || (s.at("A") == s.at("C") && s.at("B") > s.at("D"))));
    // (A B) <=lex (C D): A < C, or A == C and B <= D.
    for (const auto & s :
        enumerate("( (version 1) (variables (A 0 2) (B 0 2) (C 0 2) (D 0 2)) (constraints (_1 lex_less_equal (A B) (C D))) (prob_type enumerate) )"))
        CHECK(((s.at("A") < s.at("C")) || (s.at("A") == s.at("C") && s.at("B") <= s.at("D"))));
}

TEST_CASE("read_scp: a half-reified lex comparison enumerates correctly")
{
    // Z == 1  =>  (A B) >lex (C D) (a half reification: Z == 0 leaves it free).
    for (const auto & s : enumerate("( (version 1) (variables (Z 0 1) (A 0 1) (B 0 1) (C 0 1) (D 0 1)) (constraints (_1 lex_greater_than_if (Z = 1) "
                                    "(A B) (C D))) (prob_type enumerate) )"))
        if (s.at("Z") == 1)
            CHECK(((s.at("A") > s.at("C")) || (s.at("A") == s.at("C") && s.at("B") > s.at("D"))));
}

TEST_CASE("read_scp: a fully-reified lex comparison enumerates correctly")
{
    // Z == 1  iff  (A B) <=lex (C D).
    for (const auto & s : enumerate("( (version 1) (variables (Z 0 1) (A 0 1) (B 0 1) (C 0 1) (D 0 1)) (constraints (_1 lex_less_equal_iff (Z = 1) "
                                    "(A B) (C D))) (prob_type enumerate) )")) {
        bool le = (s.at("A") < s.at("C")) || (s.at("A") == s.at("C") && s.at("B") <= s.at("D"));
        CHECK((s.at("Z") == 1) == le);
    }
}

TEST_CASE("read_scp: global cardinality enumerates correctly")
{
    // CA counts the 0s among X, Y, Z; CB counts the 1s.
    for (const auto & s : enumerate("( (version 1) (variables (X 0 2) (Y 0 2) (Z 0 2) (CA 0 3) (CB 0 3)) (constraints (_1 boundsglobalcardinality (X "
                                    "Y Z) (0 1) (CA CB))) (prob_type enumerate) )")) {
        CHECK(s.at("CA") == (s.at("X") == 0) + (s.at("Y") == 0) + (s.at("Z") == 0));
        CHECK(s.at("CB") == (s.at("X") == 1) + (s.at("Y") == 1) + (s.at("Z") == 1));
    }
    // The closed form additionally confines every variable to a cover value, so
    // the value 2 is excluded (the gac keyword selects the GAC propagator; the
    // solution set is the same).
    for (const auto & s : enumerate("( (version 1) (variables (X 0 2) (Y 0 2) (Z 0 2) (CA 0 3) (CB 0 3)) (constraints (_1 gacglobalcardinalityclosed "
                                    "(X Y Z) (0 1) (CA CB))) (prob_type enumerate) )")) {
        CHECK((s.at("X") == 0 || s.at("X") == 1));
        CHECK(s.at("CA") + s.at("CB") == 3);
    }
}

TEST_CASE("read_scp: in with a mix of integer and variable values")
{
    // V in {0, 3} (constants) or = W (a variable).
    auto solutions = enumerate(R"(
        (
            (version 1)
            (variables (V 0 5) (W 0 5))
            (constraints (_1 in (0 3 W) V))
            (prob_type enumerate)
        ))");

    for (const auto & s : solutions)
        CHECK((s.at("V") == 0 || s.at("V") == 3 || s.at("V") == s.at("W")));
    // Every (V, W) with V in {0,3} (6 W values each) plus V == W (the rest).
    CHECK(! solutions.empty());
}

TEST_CASE("read_scp: comparisons enumerate correctly")
{
    for (const auto & s : enumerate("( (version 1) (variables (X 0 2) (Y 0 2)) (constraints (_1 less_than X Y)) (prob_type enumerate) )"))
        CHECK(s.at("X") < s.at("Y"));
    for (const auto & s : enumerate("( (version 1) (variables (X 0 2) (Y 0 2)) (constraints (_1 less_equal X Y)) (prob_type enumerate) )"))
        CHECK(s.at("X") <= s.at("Y"));
}

TEST_CASE("read_scp: a fully-reified comparison enumerates correctly")
{
    // C == 1  iff  X <= Y.
    for (const auto & s :
        enumerate("( (version 1) (variables (X 0 2) (Y 0 2) (C 0 1)) (constraints (_1 less_equal_iff (C = 1) X Y)) (prob_type enumerate) )"))
        CHECK((s.at("C") == 1) == (s.at("X") <= s.at("Y")));
}

TEST_CASE("read_scp: comparisons survive write -> read -> write unchanged")
{
    Problem original;
    auto x = original.create_integer_variable(-2_i, 2_i, "X");
    auto y = original.create_integer_variable(-2_i, 2_i, "Y");
    auto z = original.create_integer_variable(-2_i, 2_i, "Z");
    auto c = original.create_integer_variable(0_i, 1_i, "C");
    original.post(LessThanEqual{x, y});              // plain, or_equal
    original.post(GreaterThan{y, z});                // operands swapped on write
    original.post(LessThanEqualIff{x, z, c == 1_i}); // fully reified, with a condition
    auto scp_a = prove_to_scp(original, "scp_reader_cmp_a");

    Problem rebuilt;
    read_scp(rebuilt, scp_a);
    auto scp_b = prove_to_scp(rebuilt, "scp_reader_cmp_b");

    CHECK(scp_a == scp_b);
    CHECK_FALSE(scp_a.empty());
}

TEST_CASE("read_scp: lex comparisons survive write -> read -> write unchanged")
{
    Problem original;
    auto a0 = original.create_integer_variable(0_i, 2_i, "A0");
    auto a1 = original.create_integer_variable(0_i, 2_i, "A1");
    auto b0 = original.create_integer_variable(0_i, 2_i, "B0");
    auto b1 = original.create_integer_variable(0_i, 2_i, "B1");
    auto c = original.create_integer_variable(0_i, 1_i, "C");
    original.post(LexGreaterThan{{a0, a1}, {b0, b1}});                // plain greater
    original.post(LexLessThanEqualIff{{a0, a1}, {b0, b1}, c == 1_i}); // or-equal, swapped on write, reified
    auto scp_a = prove_to_scp(original, "scp_reader_lex_a");

    Problem rebuilt;
    read_scp(rebuilt, scp_a);
    auto scp_b = prove_to_scp(rebuilt, "scp_reader_lex_b");

    CHECK(scp_a == scp_b);
    CHECK_FALSE(scp_a.empty());
}

TEST_CASE("read_scp: linear constraints enumerate correctly")
{
    // X + Y == 3
    for (const auto & s : enumerate("( (version 1) (variables (X 0 3) (Y 0 3)) (constraints (_1 lin_equals (1 X 1 Y) 3)) (prob_type enumerate) )"))
        CHECK(s.at("X") + s.at("Y") == 3);
    // X - Y <= 1
    for (const auto & s :
        enumerate("( (version 1) (variables (X 0 3) (Y 0 3)) (constraints (_1 lin_less_equal (1 X -1 Y) 1)) (prob_type enumerate) )"))
        CHECK(s.at("X") - s.at("Y") <= 1);
    // X + Y != 2
    for (const auto & s :
        enumerate("( (version 1) (variables (X 0 2) (Y 0 2)) (constraints (_1 lin_not_equals (1 X 1 Y) 2)) (prob_type enumerate) )"))
        CHECK(s.at("X") + s.at("Y") != 2);
}

TEST_CASE("read_scp: a reified linear constraint enumerates correctly")
{
    // C == 1  iff  X + Y == 3.
    for (const auto & s :
        enumerate("( (version 1) (variables (X 0 3) (Y 0 3) (C 0 1)) (constraints (_1 lin_equals_iff (C = 1) (1 X 1 Y) 3)) (prob_type enumerate) )"))
        CHECK((s.at("C") == 1) == (s.at("X") + s.at("Y") == 3));
}

TEST_CASE("read_scp: linear constraints survive write -> read -> write unchanged")
{
    Problem original;
    auto x = original.create_integer_variable(-2_i, 2_i, "X");
    auto y = original.create_integer_variable(-2_i, 2_i, "Y");
    auto z = original.create_integer_variable(-2_i, 2_i, "Z");
    auto c = original.create_integer_variable(0_i, 1_i, "C");
    original.post(LinearEquality{WeightedSum{} + 1_i * x + 1_i * y, 1_i});
    original.post(LinearLessThanEqual{WeightedSum{} + 1_i * x + -1_i * z, 2_i});
    original.post(LinearNotEquals{WeightedSum{} + 2_i * y, 0_i});
    original.post(LinearEqualityIff{WeightedSum{} + 1_i * x + 1_i * z, 1_i, c == 1_i});
    original.post(LinearNotEqualsIff{WeightedSum{} + 1_i * y + 1_i * z, 0_i, c == 1_i}); // flipped_cond path
    auto scp_a = prove_to_scp(original, "scp_reader_lin_a");

    Problem rebuilt;
    read_scp(rebuilt, scp_a);
    auto scp_b = prove_to_scp(rebuilt, "scp_reader_lin_b");

    CHECK(scp_a == scp_b);
    CHECK_FALSE(scp_a.empty());
}

TEST_CASE("read_scp: multiply enumerates correctly")
{
    auto solutions = enumerate(R"(
        (
            (version 1)
            (variables (X 1 3) (Y 1 3) (Z 1 9))
            (constraints (_1 multiply X Y Z))
            (prob_type enumerate)
        ))");

    CHECK(solutions.size() == 9);
    for (const auto & s : solutions)
        CHECK(s.at("X") * s.at("Y") == s.at("Z"));
}

TEST_CASE("read_scp: multiply constraints survive write -> read -> write unchanged")
{
    Problem original;
    auto x = original.create_integer_variable(-2_i, 2_i, "X");
    auto y = original.create_integer_variable(1_i, 3_i, "Y");
    auto z = original.create_integer_variable(-6_i, 6_i, "Z");
    original.post(Multiply{x, y, z}); // plain: multiply
    original.post(Multiply{x, x, z}); // aliased: still multiply
    // (a view operand also writes a multiply term, but view terms are lists and
    // the reader's resolve_variable only handles atoms, as for every other
    // constraint -- so no view case here)
    original.post(Multiply{constant_variable(2_i), y, z}); // constant operand: resolves to lin_equals
    original.post(Multiply{x, y, z});                      // the plain three-distinct-variables shape
    auto scp_a = prove_to_scp(original, "scp_reader_multiply_a");

    Problem rebuilt;
    read_scp(rebuilt, scp_a);
    auto scp_b = prove_to_scp(rebuilt, "scp_reader_multiply_b");

    CHECK(scp_a == scp_b);
    CHECK_FALSE(scp_a.empty());
}

TEST_CASE("read_scp: divide and modulus enumerate correctly")
{
    auto div_solutions = enumerate(R"(
        (
            (version 1)
            (variables (X -3 3) (Y -2 2) (Q -3 3))
            (constraints (_1 divide X Y Q))
            (prob_type enumerate)
        ))");

    CHECK(! div_solutions.empty());
    for (const auto & s : div_solutions) {
        CHECK(s.at("Y") != 0);
        if (s.at("Y") != 0)
            CHECK(s.at("X") / s.at("Y") == s.at("Q"));
    }

    auto mod_solutions = enumerate(R"(
        (
            (version 1)
            (variables (X -3 3) (Y -2 2) (R -3 3))
            (constraints (_1 modulus X Y R))
            (prob_type enumerate)
        ))");

    CHECK(! mod_solutions.empty());
    for (const auto & s : mod_solutions) {
        CHECK(s.at("Y") != 0);
        if (s.at("Y") != 0)
            CHECK(s.at("X") % s.at("Y") == s.at("R"));
    }
}

TEST_CASE("read_scp: divide and modulus survive write -> read -> write unchanged")
{
    Problem original;
    auto x = original.create_integer_variable(-3_i, 3_i, "X");
    auto y = original.create_integer_variable(-2_i, 2_i, "Y");
    auto z = original.create_integer_variable(-3_i, 3_i, "Z");
    original.post(Divide{x, y, z});
    original.post(Modulus{x, y, z});
    original.post(Divide{x, constant_variable(2_i), z}); // constant divisor: still divide
    auto scp_a = prove_to_scp(original, "scp_reader_divmod_a");

    Problem rebuilt;
    read_scp(rebuilt, scp_a);
    auto scp_b = prove_to_scp(rebuilt, "scp_reader_divmod_b");

    CHECK(scp_a == scp_b);
    CHECK_FALSE(scp_a.empty());
}

TEST_CASE("read_scp: power enumerates correctly")
{
    auto solutions = enumerate(R"(
        (
            (version 1)
            (variables (X -2 2) (K -1 3) (Z -2 8))
            (constraints (_1 power (X K Z)))
            (prob_type enumerate)
        ))");

    CHECK(! solutions.empty());
    for (const auto & s : solutions) {
        auto a = s.at("X"), b = s.at("K"), c = s.at("Z");
        if (b == 0)
            CHECK(c == 1);
        else if (a == 1)
            CHECK(c == 1);
        else if (a == -1)
            CHECK(c == ((b % 2 == 0) ? 1 : -1));
        else if (b < 0)
            CHECK((a != 0 && c == 0));
        else {
            long long r = 1;
            for (long long i = 0; i < b; ++i)
                r *= a;
            CHECK(c == r);
        }
    }
}

TEST_CASE("read_scp: power survives write -> read -> write unchanged")
{
    Problem original;
    auto x = original.create_integer_variable(-2_i, 2_i, "X");
    auto k = original.create_integer_variable(0_i, 3_i, "K");
    auto z = original.create_integer_variable(-8_i, 8_i, "Z");
    original.post(Power{x, k, z});                       // variable exponent: PowerTable
    original.post(Power{x, constant_variable(2_i), z});  // constant exponent: chain
    original.post(Power{x, constant_variable(-2_i), z}); // negative: case analysis
    auto scp_a = prove_to_scp(original, "scp_reader_power_a");

    Problem rebuilt;
    read_scp(rebuilt, scp_a);
    auto scp_b = prove_to_scp(rebuilt, "scp_reader_power_b");

    CHECK(scp_a == scp_b);
    CHECK_FALSE(scp_a.empty());
}

TEST_CASE("read_scp: equals and not_equals enumerate correctly")
{
    for (const auto & s : enumerate("( (version 1) (variables (X 0 2) (Y 0 2)) (constraints (_1 equals X Y)) (prob_type enumerate) )"))
        CHECK(s.at("X") == s.at("Y"));
    for (const auto & s : enumerate("( (version 1) (variables (X 0 2) (Y 0 2)) (constraints (_1 not_equals X Y)) (prob_type enumerate) )"))
        CHECK(s.at("X") != s.at("Y"));
    // not_equals against a constant, the way crystal_maze uses it.
    for (const auto & s : enumerate("( (version 1) (variables (X -2 2)) (constraints (_1 not_equals X 0)) (prob_type enumerate) )"))
        CHECK(s.at("X") != 0);
}

TEST_CASE("read_scp: a reified equals enumerates correctly")
{
    // C == 1  iff  X == Y.
    for (const auto & s :
        enumerate("( (version 1) (variables (X 0 2) (Y 0 2) (C 0 1)) (constraints (_1 equals_iff (C = 1) X Y)) (prob_type enumerate) )"))
        CHECK((s.at("C") == 1) == (s.at("X") == s.at("Y")));
}

TEST_CASE("read_scp: equals constraints survive write -> read -> write unchanged")
{
    Problem original;
    auto x = original.create_integer_variable(-2_i, 2_i, "X");
    auto y = original.create_integer_variable(-2_i, 2_i, "Y");
    auto z = original.create_integer_variable(-2_i, 2_i, "Z");
    auto c = original.create_integer_variable(0_i, 1_i, "C");
    original.post(Equals{x, y});
    original.post(NotEquals{x, constant_variable(0_i)}); // against a constant
    original.post(EqualsIff{x, z, c == 1_i});
    original.post(NotEqualsIff{y, z, c == 1_i}); // _neq path
    auto scp_a = prove_to_scp(original, "scp_reader_eq_a");

    Problem rebuilt;
    read_scp(rebuilt, scp_a);
    auto scp_b = prove_to_scp(rebuilt, "scp_reader_eq_b");

    CHECK(scp_a == scp_b);
    CHECK_FALSE(scp_a.empty());
}

TEST_CASE("read_scp: element enumerates correctly")
{
    const long long arr[] = {5, 7, 9, 11};

    // R = arr[I], I in 0..3 (offset 0).
    for (const auto & s :
        enumerate("( (version 1) (variables (R 0 15) (I 0 3)) (constraints (_1 element (5 7 9 11) (I 0) R)) (prob_type enumerate) )"))
        CHECK(s.at("R") == arr[s.at("I")]);

    // With an offset of 1, I in 1..4 selects arr[I - 1].
    for (const auto & s :
        enumerate("( (version 1) (variables (R 0 15) (I 1 4)) (constraints (_1 element (5 7 9 11) (I 1) R)) (prob_type enumerate) )"))
        CHECK(s.at("R") == arr[s.at("I") - 1]);

    // A variable array: R = (I == 0 ? A : B).
    for (const auto & s :
        enumerate("( (version 1) (variables (A 0 2) (B 0 2) (R 0 2) (I 0 1)) (constraints (_1 element (A B) (I 0) R)) (prob_type enumerate) )"))
        CHECK(s.at("R") == (s.at("I") == 0 ? s.at("A") : s.at("B")));
}

TEST_CASE("read_scp: count enumerates correctly")
{
    // K = #{ v in (A, B, C) : v == V }.
    for (const auto & s :
        enumerate("( (version 1) (variables (A 0 2) (B 0 2) (C 0 2) (V 0 2) (K 0 3)) (constraints (_1 count (A B C) V K)) (prob_type enumerate) )")) {
        auto k = (s.at("A") == s.at("V")) + (s.at("B") == s.at("V")) + (s.at("C") == s.at("V"));
        CHECK(s.at("K") == k);
    }
}

TEST_CASE("read_scp: element and count survive write -> read -> write unchanged")
{
    Problem original;
    auto a = original.create_integer_variable(0_i, 2_i, "A");
    auto b = original.create_integer_variable(0_i, 2_i, "B");
    auto c = original.create_integer_variable(0_i, 2_i, "C");
    auto r = original.create_integer_variable(0_i, 2_i, "R");
    auto i = original.create_integer_variable(0_i, 2_i, "I");
    auto v = original.create_integer_variable(0_i, 2_i, "V");
    auto k = original.create_integer_variable(0_i, 3_i, "K");
    vector<IntegerVariableID> arr{a, b, c};
    original.post(Element{r, {i, 0_i}, &arr}); // arr outlives the prove below
    original.post(Count{{a, b, c}, v, k});
    auto scp_a = prove_to_scp(original, "scp_reader_elemcount_a");

    Problem rebuilt;
    read_scp(rebuilt, scp_a);
    auto scp_b = prove_to_scp(rebuilt, "scp_reader_elemcount_b");

    CHECK(scp_a == scp_b);
    CHECK_FALSE(scp_a.empty());
}

TEST_CASE("read_scp: all_equal and the increasing family survive write -> read -> write unchanged")
{
    Problem original;
    auto a = original.create_integer_variable(0_i, 3_i, "A");
    auto b = original.create_integer_variable(0_i, 3_i, "B");
    auto c = original.create_integer_variable(0_i, 3_i, "C");
    auto d = original.create_integer_variable(0_i, 3_i, "D");
    original.post(AllEqual{std::vector<IntegerVariableID>{a, b}});
    original.post(Increasing{std::vector<IntegerVariableID>{b, c}});
    original.post(StrictlyIncreasing{std::vector<IntegerVariableID>{c, d}});
    original.post(Decreasing{std::vector<IntegerVariableID>{d, c}});         // exercises the descending keyword
    original.post(StrictlyDecreasing{std::vector<IntegerVariableID>{d, c}}); // ... and its strict variant
    auto scp_a = prove_to_scp(original, "scp_reader_aeqinc_a");

    Problem rebuilt;
    read_scp(rebuilt, scp_a);
    auto scp_b = prove_to_scp(rebuilt, "scp_reader_aeqinc_b");

    CHECK(scp_a == scp_b);
    CHECK_FALSE(scp_a.empty());
}

TEST_CASE("read_scp: regular enumerates correctly")
{
    // A 2-state parity DFA over {0,1}: state 0 = an even number of 1s read so
    // far (the start state and the only accepting state), state 1 = odd; reading
    // a 1 toggles the state. So the accepted words are those with an even number
    // of 1s.
    for (const auto & s : enumerate("( (version 1) (variables (X0 0 1) (X1 0 1) (X2 0 1)) (constraints (_1 regular (X0 X1 X2) 2 ( ((0 0) (1 1)) ((0 "
                                    "1) (1 0)) ) (0))) (prob_type enumerate) )"))
        CHECK((s.at("X0") + s.at("X1") + s.at("X2")) % 2 == 0);
}

TEST_CASE("read_scp: disjunctive enumerates correctly")
{
    // Two length-2 tasks in 0..3 must not overlap, so their starts differ by at
    // least 2. The strict keyword variant builds the same solution set for
    // positive lengths.
    for (const auto & s :
        enumerate("( (version 1) (variables (S0 0 3) (S1 0 3)) (constraints (_1 disjunctive (S0 S1) (2 2))) (prob_type enumerate) )")) {
        auto d = s.at("S0") - s.at("S1");
        CHECK((d >= 2 || d <= -2));
    }
    for (const auto & s :
        enumerate("( (version 1) (variables (S0 0 3) (S1 0 3)) (constraints (_1 disjunctive_strict (S0 S1) (2 2))) (prob_type enumerate) )")) {
        auto d = s.at("S0") - s.at("S1");
        CHECK((d >= 2 || d <= -2));
    }
    // Variable durations are allowed too: the length list may name variables.
    for (const auto & s :
        enumerate("( (version 1) (variables (S0 0 4) (S1 0 4) (D 1 2)) (constraints (_1 disjunctive (S0 S1) (D D))) (prob_type enumerate) )")) {
        auto d = s.at("S0") - s.at("S1");
        CHECK((d >= s.at("D") || d <= -s.at("D")));
    }
}

TEST_CASE("read_scp: disjunctive_optional enumerates correctly")
{
    // Two length-2 tasks in 0..3 that may each be absent: they need separating
    // only when both are present.
    for (const auto & s : enumerate("( (version 1) (variables (S0 0 3) (S1 0 3) (P0 0 1) (P1 0 1)) (constraints (_1 disjunctive_optional (S0 S1) (2 "
                                    "2) (P0 P1))) (prob_type enumerate) )")) {
        auto d = s.at("S0") - s.at("S1");
        CHECK((s.at("P0") == 0 || s.at("P1") == 0 || d >= 2 || d <= -2));
    }
    // The strict form differs only over zero-length tasks, which a present task
    // may not contain: task 1 has length 0, so when both are present its start
    // may not sit strictly inside 0's. This is the case that has no route
    // through Cumulative at all.
    for (const auto & s : enumerate("( (version 1) (variables (S0 0 3) (S1 0 3) (P0 0 1) (P1 0 1)) (constraints (_1 disjunctive_strict_optional (S0 "
                                    "S1) (3 0) (P0 P1))) (prob_type enumerate) )"))
        if (s.at("P0") == 1 && s.at("P1") == 1) {
            bool zero_inside = s.at("S0") < s.at("S1") && s.at("S1") < s.at("S0") + 3;
            CHECK_FALSE(zero_inside);
        }
}

TEST_CASE("read_scp: disjunctive2d enumerates correctly")
{
    // Two 2x2 rectangles in a 0..3 x 0..3 grid must not overlap, so they are
    // separated in x or in y.
    for (const auto & s : enumerate("( (version 1) (variables (X0 0 3) (X1 0 3) (Y0 0 3) (Y1 0 3)) (constraints (_1 disjunctive2d (X0 X1) (Y0 Y1) (2 "
                                    "2) (2 2))) (prob_type enumerate) )")) {
        auto dx = s.at("X0") - s.at("X1");
        auto dy = s.at("Y0") - s.at("Y1");
        CHECK((dx >= 2 || dx <= -2 || dy >= 2 || dy <= -2));
    }
}

TEST_CASE("read_scp: cumulative enumerates correctly")
{
    // Three unit-length, unit-height tasks sharing a capacity-2 resource over the
    // two time points 0..1: at most two may run at any one time, so no time point
    // is occupied by all three.
    for (const auto & s : enumerate("( (version 1) (variables (S0 0 1) (S1 0 1) (S2 0 1)) (constraints (_1 cumulative (S0 S1 S2) (1 1 1) (1 1 1) 2)) "
                                    "(prob_type enumerate) )"))
        for (long long t = 0; t <= 1; ++t)
            CHECK((s.at("S0") == t) + (s.at("S1") == t) + (s.at("S2") == t) <= 2);

    // Variable heights and a variable capacity are allowed too: the height and
    // capacity slots may name variables. Two tasks of common height H share a
    // capacity-2 resource, so they may overlap only when 2*H <= 2, i.e. H <= 1.
    for (const auto & s : enumerate("( (version 1) (variables (S0 0 1) (S1 0 1) (H 1 2) (C 2 2)) (constraints (_1 cumulative (S0 S1) (1 1) (H H) C)) "
                                    "(prob_type enumerate) )"))
        if (s.at("H") == 2)
            CHECK(s.at("S0") != s.at("S1"));
}

TEST_CASE("read_scp: regular, disjunctive, disjunctive2d and cumulative survive write -> read -> write unchanged")
{
    Problem original;
    auto x0 = original.create_integer_variable(0_i, 1_i, "X0");
    auto x1 = original.create_integer_variable(0_i, 1_i, "X1");
    auto s0 = original.create_integer_variable(0_i, 3_i, "S0");
    auto s1 = original.create_integer_variable(0_i, 3_i, "S1");
    auto y0 = original.create_integer_variable(0_i, 3_i, "Y0");
    auto y1 = original.create_integer_variable(0_i, 3_i, "Y1");
    auto p0 = original.create_integer_variable(0_i, 1_i, "P0");
    auto p1 = original.create_integer_variable(0_i, 1_i, "P1");
    original.post(Regular{std::vector<IntegerVariableID>{x0, x1}, 2,
        std::vector<std::unordered_map<Integer, long>>{{{0_i, 0}, {1_i, 1}}, {{0_i, 1}, {1_i, 0}}}, std::vector<long>{0}});
    original.post(Disjunctive{std::vector<IntegerVariableID>{s0, s1}, std::vector<Integer>{2_i, 2_i}}); // strict -> disjunctive_strict
    original.post(
        Disjunctive{std::vector<IntegerVariableID>{s0, s1}, std::vector<Integer>{2_i, 2_i}}.with_strict(false)); // non-strict -> disjunctive
    original.post(Disjunctive{std::vector<IntegerVariableID>{s0, s1}, as_constant_variables(std::vector<Integer>{2_i, 2_i}),
        std::vector<IntegerVariableID>{p0, p1}}); // -> disjunctive_strict_optional
    original.post(Disjunctive2D{std::vector<IntegerVariableID>{s0, s1}, std::vector<IntegerVariableID>{y0, y1}, std::vector<Integer>{2_i, 2_i},
        std::vector<Integer>{2_i, 2_i}}
            .with_strict(false));
    original.post(Cumulative{std::vector<IntegerVariableID>{s0, s1}, std::vector<Integer>{2_i, 2_i}, std::vector<Integer>{1_i, 1_i}, 2_i});
    auto scp_a = prove_to_scp(original, "scp_reader_regdisj_a");

    Problem rebuilt;
    read_scp(rebuilt, scp_a);
    auto scp_b = prove_to_scp(rebuilt, "scp_reader_regdisj_b");

    CHECK(scp_a == scp_b);
    CHECK_FALSE(scp_a.empty());
}

TEST_CASE("read_scp: table enumerates correctly")
{
    // Allow exactly three of the nine pairs.
    auto solutions =
        enumerate("( (version 1) (variables (A 0 2) (B 0 2)) (constraints (_1 table ((0 1) (1 2) (2 0)) (A B))) (prob_type enumerate) )");
    CHECK(solutions == set<map<string, long long>>{{{"A", 0}, {"B", 1}}, {{"A", 1}, {"B", 2}}, {{"A", 2}, {"B", 0}}});

    // A wildcard allows a whole slice: (0 *) admits every tuple with A = 0.
    for (const auto & s : enumerate("( (version 1) (variables (A 0 2) (B 0 2)) (constraints (_1 table ((0 *)) (A B))) (prob_type enumerate) )"))
        CHECK(s.at("A") == 0);
}

TEST_CASE("read_scp: negative_table enumerates correctly")
{
    // Forbid the three diagonal tuples, leaving exactly the off-diagonal pairs.
    auto solutions =
        enumerate("( (version 1) (variables (A 0 2) (B 0 2)) (constraints (_1 negative_table ((0 0) (1 1) (2 2)) (A B))) (prob_type enumerate) )");
    CHECK(solutions.size() == 6);
    for (const auto & s : solutions)
        CHECK(s.at("A") != s.at("B"));

    // A wildcard forbids a whole slice: (0 *) rules out every tuple with A = 0.
    for (const auto & s :
        enumerate("( (version 1) (variables (A 0 2) (B 0 2)) (constraints (_1 negative_table ((0 *)) (A B))) (prob_type enumerate) )"))
        CHECK(s.at("A") != 0);
}

TEST_CASE("read_scp: smart_table enumerates correctly")
{
    // A two-row table exercising every entry kind: row 1 = (A = 1) and B in {2,3}
    // (a unary-value and a unary-set entry), row 2 = (A = B) (a binary entry). The
    // disjunction admits A = B, plus A = 1 paired with B in {2,3}.
    auto solutions = enumerate("( (version 1) (variables (A 0 3) (B 0 3)) (constraints (_1 smart_table ( ((A = 1) (B in (2 3))) ((A = B)) ) (A B))) "
                               "(prob_type enumerate) )");
    CHECK(solutions.size() == 6);
    for (const auto & s : solutions)
        CHECK(((s.at("A") == 1 && (s.at("B") == 2 || s.at("B") == 3)) || s.at("A") == s.at("B")));
}

TEST_CASE("read_scp: the table family survives write -> read -> write unchanged")
{
    Problem original;
    auto a = original.create_integer_variable(0_i, 3_i, "A");
    auto b = original.create_integer_variable(0_i, 3_i, "B");
    // A wildcard tuple keeps the WildcardTuples path; the all-integer tuple checks
    // that a wildcard-free row still round-trips inside it. Positive and negative
    // tables share the writer, so the positive table covers the SimpleTuples path.
    original.post(Table{std::vector<IntegerVariableID>{a, b}, SimpleTuples{{0_i, 1_i}, {2_i, 3_i}}});
    original.post(NegativeTable{std::vector<IntegerVariableID>{a, b}, WildcardTuples{{0_i, Wildcard{}}, {1_i, 2_i}}});
    // Every smart-entry kind: binary, unary value, unary set (in) and unary set (notin).
    SmartTuples tuples;
    tuples.push_back(std::vector<SmartEntry>{SmartTable::less_than(a, b), SmartTable::in_set(a, std::vector<Integer>{1_i, 2_i})});
    tuples.push_back(std::vector<SmartEntry>{SmartTable::equals(a, 1_i), SmartTable::not_in_set(b, std::vector<Integer>{0_i})});
    original.post(SmartTable{std::vector<IntegerVariableID>{a, b}, tuples});
    auto scp_a = prove_to_scp(original, "scp_reader_table_a");

    Problem rebuilt;
    read_scp(rebuilt, scp_a);
    auto scp_b = prove_to_scp(rebuilt, "scp_reader_table_b");

    CHECK(scp_a == scp_b);
    CHECK_FALSE(scp_a.empty());
}

TEST_CASE("read_scp: all_different_except enumerates correctly")
{
    // Distinct unless the value is excluded (here 2), so the only forbidden pairs
    // are the non-excluded diagonals (0,0) and (1,1).
    auto solutions = enumerate("( (version 1) (variables (A 0 2) (B 0 2)) (constraints (_1 all_different_except (A B) (2))) (prob_type enumerate) )");
    CHECK(solutions.size() == 7);
    for (const auto & s : solutions)
        CHECK((s.at("A") != s.at("B") || s.at("A") == 2));
}

TEST_CASE("read_scp: symmetric_all_different enumerates correctly")
{
    // An all_different whose assignment is an involution: reading each value as an
    // index (start 0), X[X[i]] == i.
    auto solutions = enumerate(
        "( (version 1) (variables (X0 0 2) (X1 0 2) (X2 0 2)) (constraints (_1 symmetric_all_different (X0 X1 X2) 0)) (prob_type enumerate) )");
    CHECK(solutions.size() == 4); // identity + the three transpositions
    for (const auto & s : solutions) {
        std::vector<long long> x{s.at("X0"), s.at("X1"), s.at("X2")};
        for (size_t i = 0; i < x.size(); ++i)
            CHECK(x[x[i]] == static_cast<long long>(i));
    }
}

TEST_CASE("read_scp: at_most_one enumerates correctly")
{
    // At most one of the variables equals the value 1.
    auto solutions = enumerate("( (version 1) (variables (A 0 2) (B 0 2) (C 0 2)) (constraints (_1 at_most_one (A B C) 1)) (prob_type enumerate) )");
    for (const auto & s : solutions)
        CHECK((s.at("A") == 1) + (s.at("B") == 1) + (s.at("C") == 1) <= 1);
}

TEST_CASE("read_scp: among enumerates correctly")
{
    // how_many counts the variables taking a value of interest (here just 1).
    auto solutions = enumerate("( (version 1) (variables (A 0 2) (B 0 2) (N 0 2)) (constraints (_1 among (A B) (1) N)) (prob_type enumerate) )");
    CHECK(solutions.size() == 9); // one per (A, B) pair, N is then determined
    for (const auto & s : solutions)
        CHECK(s.at("N") == (s.at("A") == 1) + (s.at("B") == 1));
}

TEST_CASE("read_scp: the precedence family enumerates correctly")
{
    // "Every occurrence of t has a strictly earlier occurrence of s."
    auto precedes = [](const std::vector<long long> & seq, long long s, long long t) {
        for (size_t i = 0; i < seq.size(); ++i)
            if (seq[i] == t) {
                bool earlier_s = false;
                for (size_t j = 0; j < i; ++j)
                    if (seq[j] == s)
                        earlier_s = true;
                if (! earlier_s)
                    return false;
            }
        return true;
    };

    // value_precede (0 1): 1 may not appear before 0 has.
    for (const auto & s :
        enumerate("( (version 1) (variables (A 0 2) (B 0 2) (C 0 2)) (constraints (_1 value_precede (0 1) (A B C))) (prob_type enumerate) )"))
        CHECK(precedes({s.at("A"), s.at("B"), s.at("C")}, 0, 1));

    // seq_precede_chain over 0..2 is value_precede on the implicit chain [1, 2],
    // so 2 may not appear before 1 has (0 and 1 are otherwise free).
    for (const auto & s :
        enumerate("( (version 1) (variables (A 0 2) (B 0 2) (C 0 2)) (constraints (_1 seq_precede_chain (A B C))) (prob_type enumerate) )"))
        CHECK(precedes({s.at("A"), s.at("B"), s.at("C")}, 1, 2));
}

TEST_CASE("read_scp: the remaining globals survive write -> read -> write unchanged")
{
    Problem original;
    auto a = original.create_integer_variable(0_i, 3_i, "A");
    auto b = original.create_integer_variable(0_i, 3_i, "B");
    auto c = original.create_integer_variable(0_i, 3_i, "C");
    auto n = original.create_integer_variable(0_i, 3_i, "N");
    original.post(AllDifferentExcept{std::vector<IntegerVariableID>{a, b, c}, std::vector<Integer>{0_i}});
    original.post(SymmetricAllDifferent{std::vector<IntegerVariableID>{a, b, c, n}});
    original.post(AtMostOne{std::vector<IntegerVariableID>{a, b, c}, 1_c});
    original.post(Among{std::vector<IntegerVariableID>{a, b, c}, std::vector<Integer>{1_i, 2_i}, n});
    original.post(ValuePrecede{std::vector<Integer>{0_i, 1_i}, std::vector<IntegerVariableID>{a, b, c}});
    original.post(SeqPrecedeChain{std::vector<IntegerVariableID>{a, b, c}});
    auto scp_a = prove_to_scp(original, "scp_reader_globals_a");

    Problem rebuilt;
    read_scp(rebuilt, scp_a);
    auto scp_b = prove_to_scp(rebuilt, "scp_reader_globals_b");

    CHECK(scp_a == scp_b);
    CHECK_FALSE(scp_a.empty());
}

TEST_CASE("read_scp: reachable enumerates correctly")
{
    // A three-node path 0 - 1 - 2 with the root pinned to node 0: the selected
    // subgraph is {0}, {0,1} or {0,1,2}, each with exactly the edges it needs.
    auto solutions = enumerate("( (version 1) (variables (R 0 0) (N0 0 1) (N1 0 1) (N2 0 1) (E0 0 1) (E1 0 1)) "
                               "(constraints (_1 reachable (0 1) (1 2) R (N0 N1 N2) (E0 E1))) (prob_type enumerate) )");
    CHECK(solutions.size() == 3);
    for (const auto & s : solutions) {
        CHECK(s.at("N0") == 1);
        CHECK(s.at("E0") == s.at("N1"));
        CHECK(s.at("E1") == s.at("N2"));
        CHECK((s.at("N1") == 1 || s.at("N2") == 0));
    }

    // Directed, so node 0 is only reachable from itself: pinning the root to node
    // 2 leaves the same chain running the other way.
    auto directed = enumerate("( (version 1) (variables (R 2 2) (N0 0 1) (N1 0 1) (N2 0 1) (E0 0 1) (E1 0 1)) "
                              "(constraints (_1 dreachable (0 1) (1 2) R (N0 N1 N2) (E0 E1))) (prob_type enumerate) )");
    CHECK(directed.size() == 1);
    for (const auto & s : directed) {
        CHECK(s.at("N2") == 1);
        CHECK(s.at("N0") == 0);
        CHECK(s.at("N1") == 0);
    }
}

TEST_CASE("read_scp: reachable survives write -> read -> write unchanged")
{
    Problem original;
    auto r = original.create_integer_variable(0_i, 2_i, "R");
    std::vector<IntegerVariableID> ns, es;
    for (int i = 0; i < 3; ++i)
        ns.push_back(original.create_integer_variable(0_i, 1_i, "N" + std::to_string(i)));
    for (int e = 0; e < 2; ++e)
        es.push_back(original.create_integer_variable(0_i, 1_i, "E" + std::to_string(e)));
    original.post(Reachable{{{0, 1}, {1, 2}}, r, ns, es});
    original.post(DReachable{{{0, 1}, {1, 2}}, r, ns, es});
    auto scp_a = prove_to_scp(original, "scp_reader_reachable_a");

    Problem rebuilt;
    read_scp(rebuilt, scp_a);
    auto scp_b = prove_to_scp(rebuilt, "scp_reader_reachable_b");

    CHECK(scp_a == scp_b);
    CHECK_FALSE(scp_a.empty());
}

TEST_CASE("read_scp: element_2d enumerates correctly")
{
    // result = array[i][j] over a constant 2x2 array; each (i, j) determines R.
    auto solutions = enumerate(
        "( (version 1) (variables (I 0 1) (J 0 1) (R 0 9)) (constraints (_1 element_2d ((1 2) (3 4)) (I 0) (J 0) R)) (prob_type enumerate) )");
    CHECK(solutions.size() == 4);
    for (const auto & s : solutions) {
        long long expected[2][2] = {{1, 2}, {3, 4}};
        CHECK(s.at("R") == expected[s.at("I")][s.at("J")]);
    }
}

TEST_CASE("read_scp: knapsack enumerates correctly")
{
    // Two coefficient rows (weight and profit): W = 2*X0 + 3*X1, P = 3*X0 + 4*X1.
    auto solutions = enumerate("( (version 1) (variables (X0 0 1) (X1 0 1) (W 0 5) (P 0 7)) (constraints (_1 knapsack ((2 3) (3 4)) (X0 X1) (W P))) "
                               "(prob_type enumerate) )");
    CHECK(solutions.size() == 4); // one per (X0, X1) subset, totals determined
    for (const auto & s : solutions) {
        CHECK(s.at("W") == 2 * s.at("X0") + 3 * s.at("X1"));
        CHECK(s.at("P") == 3 * s.at("X0") + 4 * s.at("X1"));
    }
}

TEST_CASE("read_scp: element_2d and knapsack survive write -> read -> write unchanged")
{
    Problem original;
    auto a00 = original.create_integer_variable(0_i, 3_i, "A00");
    auto a01 = original.create_integer_variable(0_i, 3_i, "A01");
    auto a10 = original.create_integer_variable(0_i, 3_i, "A10");
    auto a11 = original.create_integer_variable(0_i, 3_i, "A11");
    auto i = original.create_integer_variable(0_i, 1_i, "I");
    auto j = original.create_integer_variable(0_i, 1_i, "J");
    auto r = original.create_integer_variable(0_i, 3_i, "R");
    auto w = original.create_integer_variable(0_i, 9_i, "W");
    original.post(Element2D{r, std::pair{i, 0_i}, std::pair{j, 0_i}, std::vector<std::vector<IntegerVariableID>>{{a00, a01}, {a10, a11}}});
    original.post(Knapsack{
        std::vector<std::vector<Integer>>{{2_i, 3_i, 4_i}}, std::vector<IntegerVariableID>{a00, a01, a10}, std::vector<IntegerVariableID>{w}});
    auto scp_a = prove_to_scp(original, "scp_reader_element2d_a");

    Problem rebuilt;
    read_scp(rebuilt, scp_a);
    auto scp_b = prove_to_scp(rebuilt, "scp_reader_element2d_b");

    CHECK(scp_a == scp_b);
    CHECK_FALSE(scp_a.empty());
}

TEST_CASE("read_scp: a constant integer can stand in for a variable anywhere")
{
    // An abs operand that is a constant: Y = |3|.
    CHECK(
        enumerate("( (version 1) (variables (Y 0 5)) (constraints (_1 abs 3 Y)) (prob_type enumerate) )") == set<map<string, long long>>{{{"Y", 3}}});

    // A constant member of all_different: A, 1, B all distinct, so A,B in {0,2}.
    auto all_diff = enumerate("( (version 1) (variables (A 0 2) (B 0 2)) (constraints (_1 all_different (A 1 B))) (prob_type enumerate) )");
    CHECK(all_diff == set<map<string, long long>>{{{"A", 0}, {"B", 2}}, {{"A", 2}, {"B", 0}}});
}

TEST_CASE("read_scp: constraint labels and variable names round-trip via the map")
{
    Problem problem;
    auto model = read_scp(problem, "( (version 1) (variables (X 0 1) (Y 0 1)) (constraints (_1 abs X Y)) (prob_type enumerate) )");
    CHECK(model.variables.size() == 2);
    CHECK(model.variables.contains("X"));
    CHECK(model.variables.contains("Y"));
    CHECK_FALSE(model.minimise_variable);
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

TEST_CASE("read_scp: logical constraints survive write -> read -> write unchanged")
{
    // The and / or / parity forms write each operand as a reification tuple;
    // round-tripping them (incl. the != 0 operands the variable-list
    // constructors build) must be byte-stable.
    Problem original;
    auto b1 = original.create_integer_variable(0_i, 1_i, "B1");
    auto b2 = original.create_integer_variable(0_i, 1_i, "B2");
    auto y = original.create_integer_variable(0_i, 1_i, "Y");
    original.post(And{std::vector<IntegerVariableID>{b1, b2}, y});
    original.post(Or{std::vector<IntegerVariableID>{b1, b2}, y});
    original.post(ParityOdd{std::vector<IntegerVariableID>{b1, b2}});
    auto scp_a = prove_to_scp(original, "scp_reader_logical_roundtrip_a");

    Problem rebuilt;
    read_scp(rebuilt, scp_a);
    auto scp_b = prove_to_scp(rebuilt, "scp_reader_logical_roundtrip_b");

    CHECK(scp_a == scp_b);
    CHECK_FALSE(scp_a.empty());
}

TEST_CASE("read_scp: an out-of-order auto-number is rejected, not silently relabelled")
{
    // A single constraint labelled _2 would auto-number to _1 on re-post, so
    // post_autonumbered rejects the mismatch instead of quietly changing it.
    CHECK_THROWS_AS(enumerate("( (version 1) (variables (X 0 1) (Y 0 1)) (constraints (_2 abs X Y)) (prob_type enumerate) )"), NamingError);
}

TEST_CASE("read_scp: unsupported and malformed input throws")
{
    CHECK_THROWS_AS(enumerate("( (version 1) (variables (X 0 1)) (constraints (_1 frobnicate X)) (prob_type enumerate) )"), ScpReadError);
    CHECK_THROWS_AS(enumerate("( (version 1) (variables (X 0)) (constraints) (prob_type enumerate) )"), ScpReadError);      // bad var decl
    CHECK_THROWS_AS(enumerate("( (version 1) (variables (X zero 1)) (constraints) (prob_type enumerate) )"), ScpReadError); // non-integer bound
    CHECK_THROWS_AS(enumerate("not an s-expr ("), innards::SExprParseError);
}

TEST_CASE("read_scp: the version header is mandatory, and must be exactly 1")
{
    CHECK_NOTHROW(enumerate("( (version 1) (variables (X 0 1)) (constraints) (prob_type enumerate) )"));

    // The pre-version layout is not read on a guess, and neither is any other
    // version: a different number means a different grammar.
    CHECK_THROWS_AS(enumerate("( ( (X 0 1) ) ( ) )"), ScpReadError);
    CHECK_THROWS_AS(enumerate("( (variables (X 0 1)) (constraints) (prob_type enumerate) )"), ScpReadError);
    CHECK_THROWS_AS(enumerate("( (version 0) (variables (X 0 1)) (constraints) (prob_type enumerate) )"), ScpReadError);
    CHECK_THROWS_AS(enumerate("( (version 2) (variables (X 0 1)) (constraints) (prob_type enumerate) )"), ScpReadError);
    CHECK_THROWS_AS(enumerate("( (version one) (variables (X 0 1)) (constraints) (prob_type enumerate) )"), ScpReadError);
    CHECK_THROWS_AS(enumerate("( (version) (variables (X 0 1)) (constraints) (prob_type enumerate) )"), ScpReadError);
    CHECK_THROWS_AS(enumerate("( (version 1 1) (variables (X 0 1)) (constraints) (prob_type enumerate) )"), ScpReadError);
}

TEST_CASE("read_scp: all four sections are required, labelled and in order")
{
    // Both the keyword and the position have to line up, so a missing,
    // misspelled, reordered or extra section is an error rather than something
    // to search past.
    CHECK_THROWS_AS(enumerate("( (version 1) (variables (X 0 1)) (constraints) )"), ScpReadError);
    CHECK_THROWS_AS(enumerate("( (version 1) (variables (X 0 1)) (constraints) (prob_type enumerate) (extra) )"), ScpReadError);
    CHECK_THROWS_AS(enumerate("( (version 1) (constraints) (variables (X 0 1)) (prob_type enumerate) )"), ScpReadError);
    CHECK_THROWS_AS(enumerate("( (version 1) (vars (X 0 1)) (constraints) (prob_type enumerate) )"), ScpReadError);
    CHECK_THROWS_AS(enumerate("( (version 1) (variables (X 0 1)) (constraint) (prob_type enumerate) )"), ScpReadError);
}

TEST_CASE("read_scp: the prob_type spec is checked, and a malformed one throws")
{
    // decide / enumerate are bare atoms and the objectives are lists. None of
    // them is posted to the Problem, so all four still enumerate here -- but a
    // spec cake_pb_cp would reject must not pass silently either.
    CHECK(enumerate("( (version 1) (variables (X 0 2)) (constraints) (prob_type decide) )").size() == 3);
    CHECK(enumerate("( (version 1) (variables (X 0 2)) (constraints) (prob_type enumerate) )").size() == 3);
    CHECK(enumerate("( (version 1) (variables (X 0 2)) (constraints) (prob_type (minimize X)) )").size() == 3);
    CHECK(enumerate("( (version 1) (variables (X 0 2)) (constraints) (prob_type (maximize X)) )").size() == 3);

    CHECK_THROWS_AS(enumerate("( (version 1) (variables (X 0 2)) (constraints) (prob_type (enumerate)) )"), ScpReadError);
    CHECK_THROWS_AS(enumerate("( (version 1) (variables (X 0 2)) (constraints) (prob_type solve) )"), ScpReadError);
    CHECK_THROWS_AS(enumerate("( (version 1) (variables (X 0 2)) (constraints) (prob_type (minimize)) )"), ScpReadError);
    CHECK_THROWS_AS(enumerate("( (version 1) (variables (X 0 2)) (constraints) (prob_type (minimize X Y)) )"), ScpReadError);
    CHECK_THROWS_AS(enumerate("( (version 1) (variables (X 0 2)) (constraints) (prob_type) )"), ScpReadError);

    // An objective naming something that is neither a declared variable nor an
    // integer constant is a typo. Optimising a constant conjured out of the name
    // would silently solve a different problem.
    CHECK_THROWS_AS(enumerate("( (version 1) (variables (X 0 2)) (constraints) (prob_type (minimize Q)) )"), ScpReadError);
}

TEST_CASE("read_scp: the objective comes back as a variable to minimise")
{
    // The objective is resolved but not posted: the caller decides whether to
    // optimise, so a Problem read from an optimisation .scp still enumerates
    // until Problem::minimise() is called with what came back.
    auto solve_objective = [](string_view scp) {
        Problem problem;
        auto model = read_scp(problem, scp);
        REQUIRE(model.minimise_variable);
        problem.minimise(*model.minimise_variable);

        map<string, long long> best;
        solve_with(problem, //
            SolveCallbacks{ //
                .solution = [&](const CurrentState & state) -> bool {
                    best.clear();
                    for (const auto & [name, id] : model.variables)
                        best.emplace(name, state(id).raw_value);
                    return true;
                }});
        return best;
    };

    // 2X + Y = 10 and P = X * Y: the product is largest at (2, 6) and (3, 4),
    // and smallest at either end of the line.
    auto scp = [](string_view sense) {
        return "( (version 1) (variables (X 0 10) (Y 0 10) (P 0 100)) (constraints (_1 lin_equals (2 X 1 Y) 10) (_2 multiply X Y P)) (prob_type (" +
            string{sense} + " P)) )";
    };

    CHECK(solve_objective(scp("maximize")).at("P") == 12);
    CHECK(solve_objective(scp("minimize")).at("P") == 0);

    // A constant objective -- what the writer renders for Problem::minimise() of
    // a constant -- resolves to a constant variable rather than being rejected
    // as an undeclared name.
    Problem problem;
    auto model = read_scp(problem, "( (version 1) (variables (X 0 2)) (constraints) (prob_type (minimize 3)) )");
    REQUIRE(model.minimise_variable);
    CHECK(*model.minimise_variable == constant_variable(3_i));
}

TEST_CASE("read_scp: an objective survives write -> read -> write unchanged")
{
    // The reader's objective mirrors Problem::optional_minimise_variable(), so
    // handing it back to Problem::minimise() must reproduce the same .scp --
    // including for maximise, which is stored as a negated view and so is the
    // case that a sense flip would silently break.
    for (bool maximise : {false, true}) {
        Problem original;
        auto x = original.create_integer_variable(0_i, 4_i, "X");
        auto y = original.create_integer_variable(0_i, 4_i, "Y");
        original.post(LessThan{x, y});
        if (maximise)
            original.maximise(x);
        else
            original.minimise(x);
        auto scp_a = prove_to_scp(original, "scp_reader_obj_a");

        Problem rebuilt;
        auto model = read_scp(rebuilt, scp_a);
        REQUIRE(model.minimise_variable);
        rebuilt.minimise(*model.minimise_variable);
        auto scp_b = prove_to_scp(rebuilt, "scp_reader_obj_b");

        CHECK(scp_a == scp_b);
        CHECK(scp_a.contains(maximise ? "(prob_type (maximize X))" : "(prob_type (minimize X))"));
    }
}

TEST_CASE("read_scp: binpacking enumerates correctly in both forms")
{
    // Two items of size 1 and 2 into two bins, so the four packings give loads
    // (0,3), (2,1), (1,2), (3,0). The loads form pins them exactly; the
    // capacities form only rules out the packings that overflow a bin of 2,
    // which is the two that put both items together.
    auto loads = enumerate(R"(
        (
            (version 1)
            (variables (I0 0 1) (I1 0 1) (L0 0 3) (L1 0 3))
            (constraints (_1 binpacking (I0 I1) (1 2) loads (L0 L1)))
            (prob_type enumerate)
        ))");

    CHECK(loads ==
        set<map<string, long long>>{
            {{"I0", 0}, {"I1", 0}, {"L0", 3}, {"L1", 0}},
            {{"I0", 0}, {"I1", 1}, {"L0", 1}, {"L1", 2}},
            {{"I0", 1}, {"I1", 0}, {"L0", 2}, {"L1", 1}},
            {{"I0", 1}, {"I1", 1}, {"L0", 0}, {"L1", 3}},
        });

    auto capacities = enumerate(R"(
        (
            (version 1)
            (variables (I0 0 1) (I1 0 1))
            (constraints (_1 binpacking (I0 I1) (1 2) capacities (2 2)))
            (prob_type enumerate)
        ))");

    CHECK(capacities == set<map<string, long long>>{{{"I0", 0}, {"I1", 1}}, {{"I0", 1}, {"I1", 0}}});
}

TEST_CASE("read_scp: mdd enumerates correctly")
{
    // Three layers over two binary variables. Layer 0 is the root; the root
    // splits on X0, and each layer-1 node accepts only the *other* value of X1,
    // reaching node 0 (accepting) -- so exactly X0 != X1.
    auto solutions = enumerate(R"(
        (
            (version 1)
            (variables (X0 0 1) (X1 0 1))
            (constraints (_1 mdd (X0 X1) (1 2 1) ((((0 0) (1 1))) (((1 0)) ((0 0)))) (0)))
            (prob_type enumerate)
        ))");

    CHECK(solutions == set<map<string, long long>>{{{"X0", 0}, {"X1", 1}}, {{"X0", 1}, {"X1", 0}}});
}

TEST_CASE("read_scp: min_distance enumerates correctly, with and without requirements")
{
    // Three sites on a line at 0, 1, 3, so D = [[0,1,3],[1,0,2],[3,2,0]]. Z is
    // the minimum pairwise distance between the two chosen sites, which for two
    // positions is just D[X0][X1] (and 0 when they coincide).
    static constexpr auto distances = "((0 1 3) (1 0 2) (3 2 0))";

    auto solutions = enumerate(std::string{R"(
        (
            (version 1)
            (variables (X0 0 2) (X1 0 2) (Z 0 3))
            (constraints (_1 min_distance (X0 X1) Z )"} +
        distances + R"())
            (prob_type enumerate)
        ))");

    CHECK(solutions.size() == 9);
    for (const auto & s : solutions) {
        static constexpr long long d[3][3] = {{0, 1, 3}, {1, 0, 2}, {3, 2, 0}};
        CHECK(s.at("Z") == d[s.at("X0")][s.at("X1")]);
    }

    // The requirements matrix additionally demands D[X0][X1] >= 3, which only
    // the two site-0/site-2 orderings meet.
    auto required = enumerate(std::string{R"(
        (
            (version 1)
            (variables (X0 0 2) (X1 0 2) (Z 0 3))
            (constraints (_1 min_distance (X0 X1) Z )"} +
        distances + " ((0 3) (0 0))" + R"())
            (prob_type enumerate)
        ))");

    CHECK(required == set<map<string, long long>>{{{"X0", 0}, {"X1", 2}, {"Z", 3}}, {{"X0", 2}, {"X1", 0}, {"Z", 3}}});
}

TEST_CASE("read_scp: nogoods enumerates correctly")
{
    // Two forbidden conjunctions over a 2x2 space, leaving the other two
    // assignments. Written as the same (variable op value) triples the
    // reification conditions use.
    auto solutions = enumerate(R"(
        (
            (version 1)
            (variables (A 0 1) (B 0 1))
            (constraints (_1 nogoods (((A = 0) (B = 0)) ((A = 1) (B = 1)))))
            (prob_type enumerate)
        ))");

    CHECK(solutions == set<map<string, long long>>{{{"A", 0}, {"B", 1}}, {{"A", 1}, {"B", 0}}});
}

TEST_CASE("read_scp: binpacking, mdd, min_distance and nogoods survive write -> read -> write unchanged")
{
    Problem original;
    auto i0 = original.create_integer_variable(0_i, 1_i, "I0");
    auto i1 = original.create_integer_variable(0_i, 1_i, "I1");
    auto l0 = original.create_integer_variable(0_i, 3_i, "L0");
    auto l1 = original.create_integer_variable(0_i, 3_i, "L1");
    auto x0 = original.create_integer_variable(0_i, 1_i, "X0");
    auto x1 = original.create_integer_variable(0_i, 1_i, "X1");
    auto s0 = original.create_integer_variable(0_i, 2_i, "S0");
    auto s1 = original.create_integer_variable(0_i, 2_i, "S1");
    auto z = original.create_integer_variable(0_i, 3_i, "Z");

    original.post(BinPacking{std::vector<IntegerVariableID>{i0, i1}, std::vector<Integer>{1_i, 2_i}, std::vector<IntegerVariableID>{l0, l1}});
    original.post(BinPacking{std::vector<IntegerVariableID>{i0, i1}, std::vector<Integer>{1_i, 2_i}, std::vector<Integer>{2_i, 2_i}});
    original.post(MDD{std::vector<IntegerVariableID>{x0, x1},
        std::vector<std::vector<std::unordered_map<Integer, long>>>{{{{0_i, 0}, {1_i, 1}}}, {{{1_i, 0}}, {{0_i, 0}}}}, std::vector<long>{1, 2, 1},
        std::vector<long>{0}});
    original.post(MinDistance{std::vector<IntegerVariableID>{s0, s1}, z, MinDistance::Matrix{{0_i, 1_i, 3_i}, {1_i, 0_i, 2_i}, {3_i, 2_i, 0_i}},
        MinDistance::Matrix{{0_i, 1_i}, {0_i, 0_i}}});
    original.post(Nogoods{std::vector<Nogood>{{x0 == 0_i, x1 == 0_i}}});

    auto scp_a = prove_to_scp(original, "scp_reader_newglobals_a");

    Problem rebuilt;
    read_scp(rebuilt, scp_a);
    auto scp_b = prove_to_scp(rebuilt, "scp_reader_newglobals_b");

    CHECK(scp_a == scp_b);
    CHECK_FALSE(scp_a.empty());
}

TEST_CASE("read_scp: every regular propagator variant writes and reads back as `regular`")
{
    // The .scp names the constraint, not the propagator, so all three variants
    // write the same `regular` term over the same automaton -- which is what
    // lets a RegularLegacy or RegularBacchus proof be checked against a
    // verified encoder that only knows `regular`.
    auto automaton = []<typename Variant_>(const std::string & basename) {
        Problem problem;
        auto a = problem.create_integer_variable(0_i, 1_i, "A");
        auto b = problem.create_integer_variable(0_i, 1_i, "B");
        problem.post(Variant_{std::vector<IntegerVariableID>{a, b}, 2,
            std::vector<std::unordered_map<Integer, long>>{{{0_i, 0}, {1_i, 1}}, {{0_i, 1}, {1_i, 0}}}, std::vector<long>{0}});
        return prove_to_scp(problem, basename);
    };

    auto scp_plain = automaton.template operator()<Regular>("scp_reader_regvariant_plain");
    auto scp_legacy = automaton.template operator()<RegularLegacy>("scp_reader_regvariant_legacy");
    auto scp_bacchus = automaton.template operator()<RegularBacchus>("scp_reader_regvariant_bacchus");

    CHECK(scp_legacy == scp_plain);
    CHECK(scp_bacchus == scp_plain);
    CHECK(scp_plain.contains("regular"));
    CHECK_FALSE(scp_plain.contains("regular_legacy"));
    CHECK_FALSE(scp_plain.contains("regular_bacchus"));

    Problem rebuilt;
    read_scp(rebuilt, scp_legacy);
    CHECK(prove_to_scp(rebuilt, "scp_reader_regvariant_rebuilt") == scp_plain);
}

TEST_CASE("read_scp: difference enumerates correctly, unreified and half-reified")
{
    // A - B <= 0 and B - A <= 1, i.e. B - 1 <= A <= B over [0,2].
    auto system = enumerate(R"(
        (
            (version 1)
            (variables (A 0 2) (B 0 2))
            (constraints (_1 difference ((A B 0) (B A 1))))
            (prob_type enumerate)
        ))");

    CHECK(system ==
        set<map<string, long long>>{{{"A", 0}, {"B", 0}}, {{"A", 0}, {"B", 1}}, {{"A", 1}, {"B", 1}}, {{"A", 1}, {"B", 2}}, {{"A", 2}, {"B", 2}}});

    // The same first edge, now only in force when C = 1. C = 0 leaves A and B
    // free, so the nine unconstrained pairs come back alongside the six that
    // satisfy A - B <= 0.
    auto reified = enumerate(R"(
        (
            (version 1)
            (variables (A 0 2) (B 0 2) (C 0 1))
            (constraints (_1 difference ((A B 0 (C = 1)))))
            (prob_type enumerate)
        ))");

    CHECK(reified.size() == 9 + 6);
    for (const auto & s : reified)
        if (s.at("C") == 1)
            CHECK(s.at("A") <= s.at("B"));
}

TEST_CASE("read_scp: difference survives write -> read -> write unchanged")
{
    Problem original;
    auto a = original.create_integer_variable(0_i, 2_i, "A");
    auto b = original.create_integer_variable(0_i, 2_i, "B");
    auto c = original.create_integer_variable(0_i, 1_i, "C");
    auto d = original.create_integer_variable(0_i, 3_i, "D");
    original.post(DifferenceConstraints{std::vector<DifferenceEdge>{{a, b, 0_i}, {b, a, 1_i}, {a, b, 2_i, c == 1_i}, {b, a, 2_i, d >= 2_i}}});
    auto scp_a = prove_to_scp(original, "scp_reader_difference_a");

    Problem rebuilt;
    read_scp(rebuilt, scp_a);
    auto scp_b = prove_to_scp(rebuilt, "scp_reader_difference_b");

    CHECK(scp_a == scp_b);
    CHECK_FALSE(scp_a.empty());

    // A condition must be written as the full (variable op value) triple. The
    // writer used to render it as a bare Literal, which for `C = 1` on a {0,1}
    // variable collapses to just `C` -- so `D >= 2` came out as `D`, and the
    // .scp described a *different* problem than the one solved.
    CHECK(scp_a.contains("(C = 1)"));
    CHECK(scp_a.contains("(D >= 2)"));
}

TEST_CASE("read_scp: a .scp whose variables are all anonymous reads back")
{
    // A variable created without a name is written `_N`, which is exactly what
    // Problem::check_name() reserves and rejects -- so the reader has to
    // recreate it anonymously rather than passing the name through, or every
    // .scp from a model that did not name its variables is unreadable.
    Problem original;
    auto x = original.create_integer_variable(0_i, 3_i);
    auto y = original.create_integer_variable(0_i, 3_i);
    original.post(LessThan{x, y});
    auto scp_a = prove_to_scp(original, "scp_reader_anon_a");
    CHECK(scp_a.contains("(_1 0 3)"));

    Problem rebuilt;
    read_scp(rebuilt, scp_a);
    auto scp_b = prove_to_scp(rebuilt, "scp_reader_anon_b");
    CHECK(scp_a == scp_b);

    // Mixed named and anonymous: the anonymous ones are numbered among
    // themselves, so a named declaration in between must not consume a number.
    Problem mixed;
    auto p = mixed.create_integer_variable(0_i, 3_i);
    auto named = mixed.create_integer_variable(0_i, 3_i, "Named");
    auto q = mixed.create_integer_variable(0_i, 3_i);
    mixed.post(LessThan{p, named});
    mixed.post(LessThan{named, q});
    auto mixed_a = prove_to_scp(mixed, "scp_reader_anon_mixed_a");

    Problem mixed_rebuilt;
    read_scp(mixed_rebuilt, mixed_a);
    CHECK(prove_to_scp(mixed_rebuilt, "scp_reader_anon_mixed_b") == mixed_a);
}

TEST_CASE("read_scp: cumulative_optional enumerates correctly")
{
    // Four same-typed variable lists in a row -- starts, lengths, heights,
    // presences -- so a re-ordering of the slots would still parse, still post,
    // and still satisfy the writer/reader symmetry checks, which only ask
    // whether the keyword resolves. These three counts pin each slot to its
    // meaning rather than just to its type.
    //
    // Base: two present length-2 tasks of height 1 against capacity 1, so they
    // cannot overlap and |S0 - S1| >= 2.
    auto base = enumerate(R"(
        (
            (version 1)
            (variables (S0 0 3) (S1 0 3) (L0 2 2) (L1 2 2) (H0 1 1) (H1 1 1) (P0 1 1) (P1 1 1) (C 1 1))
            (constraints (_1 cumulative_optional (S0 S1) (L0 L1) (H0 H1) (P0 P1) C))
            (prob_type enumerate)
        ))");

    CHECK(base.size() == 6);
    for (const auto & s : base)
        CHECK(std::abs(s.at("S0") - s.at("S1")) >= 2);

    // Heights 2 against a capacity of 1: nothing fits, even alone. This is what
    // distinguishes the heights slot from the lengths slot -- swapping them
    // would leave the base case's count unchanged.
    auto over_capacity = enumerate(R"(
        (
            (version 1)
            (variables (S0 0 3) (S1 0 3) (L0 2 2) (L1 2 2) (H0 2 2) (H1 2 2) (P0 1 1) (P1 1 1) (C 1 1))
            (constraints (_1 cumulative_optional (S0 S1) (L0 L1) (H0 H1) (P0 P1) C))
            (prob_type enumerate)
        ))");

    CHECK(over_capacity.empty());

    // Task 0 absent: it stops consuming the resource, so both starts range
    // freely and every S0 x S1 pair is a solution. This is what pins the fourth
    // list as presences.
    auto one_absent = enumerate(R"(
        (
            (version 1)
            (variables (S0 0 3) (S1 0 3) (L0 2 2) (L1 2 2) (H0 1 1) (H1 1 1) (P0 0 0) (P1 1 1) (C 1 1))
            (constraints (_1 cumulative_optional (S0 S1) (L0 L1) (H0 H1) (P0 P1) C))
            (prob_type enumerate)
        ))");

    CHECK(one_absent.size() == 16);
}

TEST_CASE("read_scp: cumulative_optional survives write -> read -> write unchanged")
{
    Problem original;
    auto s0 = original.create_integer_variable(0_i, 3_i, "S0");
    auto s1 = original.create_integer_variable(0_i, 3_i, "S1");
    auto l0 = original.create_integer_variable(2_i, 2_i, "L0");
    auto l1 = original.create_integer_variable(2_i, 2_i, "L1");
    auto h0 = original.create_integer_variable(1_i, 1_i, "H0");
    auto h1 = original.create_integer_variable(1_i, 1_i, "H1");
    auto p0 = original.create_integer_variable(0_i, 1_i, "P0");
    auto p1 = original.create_integer_variable(0_i, 1_i, "P1");
    auto c = original.create_integer_variable(1_i, 1_i, "C");
    original.post(Cumulative{std::vector<IntegerVariableID>{s0, s1}, std::vector<IntegerVariableID>{l0, l1}, std::vector<IntegerVariableID>{h0, h1},
        std::vector<IntegerVariableID>{p0, p1}, c});
    auto scp_a = prove_to_scp(original, "scp_reader_cumulative_optional_a");

    Problem rebuilt;
    read_scp(rebuilt, scp_a);
    auto scp_b = prove_to_scp(rebuilt, "scp_reader_cumulative_optional_b");

    CHECK(scp_a == scp_b);
    // The slot order is what this is really guarding: the presences list sits
    // between the heights and the capacity, where the FlatZinc builtin puts it.
    CHECK(scp_a.contains("(S0 S1) (L0 L1) (H0 H1) (P0 P1) C"));
}
