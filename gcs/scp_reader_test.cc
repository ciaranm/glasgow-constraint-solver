#include <gcs/constraints/abs.hh>
#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/all_equal.hh>
#include <gcs/constraints/circuit.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/count.hh>
#include <gcs/constraints/disjunctive.hh>
#include <gcs/constraints/disjunctive_2d.hh>
#include <gcs/constraints/element.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/global_cardinality.hh>
#include <gcs/constraints/in.hh>
#include <gcs/constraints/increasing.hh>
#include <gcs/constraints/lex.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/constraints/min_max.hh>
#include <gcs/constraints/regular/regular.hh>
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

    // --prove a problem to `basename`, returning the .scp it wrote.
    auto prove_to_scp(Problem & problem, const std::string & basename) -> std::string
    {
        solve_with(problem, SolveCallbacks{},
            std::make_optional<ProofOptions>(ProofFileNames{basename}));
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

TEST_CASE("read_scp: all_equal enumerates correctly")
{
    auto solutions = enumerate(R"(
        (
            ( (A 0 2) (B 0 2) (C 0 2) )
            ( (_1 all_equal (A B C)) )
        ))");

    CHECK(solutions == set<map<string, long long>>{{{"A", 0}, {"B", 0}, {"C", 0}}, {{"A", 1}, {"B", 1}, {"C", 1}}, {{"A", 2}, {"B", 2}, {"C", 2}}});
}

TEST_CASE("read_scp: the increasing family enumerates correctly")
{
    for (const auto & s : enumerate("( ( (X 0 2) (Y 0 2) (Z 0 2) ) ( (_1 increasing (X Y Z)) ) )"))
        CHECK((s.at("X") <= s.at("Y") && s.at("Y") <= s.at("Z")));
    for (const auto & s : enumerate("( ( (X 0 3) (Y 0 3) (Z 0 3) ) ( (_1 strictly_increasing (X Y Z)) ) )"))
        CHECK((s.at("X") < s.at("Y") && s.at("Y") < s.at("Z")));
    for (const auto & s : enumerate("( ( (X 0 2) (Y 0 2) (Z 0 2) ) ( (_1 decreasing (X Y Z)) ) )"))
        CHECK((s.at("X") >= s.at("Y") && s.at("Y") >= s.at("Z")));
    for (const auto & s : enumerate("( ( (X 0 3) (Y 0 3) (Z 0 3) ) ( (_1 strictly_decreasing (X Y Z)) ) )"))
        CHECK((s.at("X") > s.at("Y") && s.at("Y") > s.at("Z")));
}

TEST_CASE("read_scp: circuit enumerates the Hamiltonian cycles")
{
    // Successor of each of three nodes; the only single cycles are the two
    // directed 3-cycles.
    auto solutions = enumerate(R"(
        (
            ( (A 0 2) (B 0 2) (C 0 2) )
            ( (_1 circuit (A B C)) )
        ))");

    CHECK(solutions == set<map<string, long long>>{{{"A", 1}, {"B", 2}, {"C", 0}}, {{"A", 2}, {"B", 0}, {"C", 1}}});
}

TEST_CASE("read_scp: array_min / array_max enumerate correctly")
{
    for (const auto & s : enumerate("( ( (X 0 2) (Y 0 2) (Z 0 2) (R 0 2) ) ( (_1 array_min (X Y Z) R) ) )"))
        CHECK(s.at("R") == std::min({s.at("X"), s.at("Y"), s.at("Z")}));
    for (const auto & s : enumerate("( ( (X 0 2) (Y 0 2) (Z 0 2) (R 0 2) ) ( (_1 array_max (X Y Z) R) ) )"))
        CHECK(s.at("R") == std::max({s.at("X"), s.at("Y"), s.at("Z")}));
}

TEST_CASE("read_scp: lex comparisons enumerate correctly")
{
    // (A B) >lex (C D): A > C, or A == C and B > D.
    for (const auto & s : enumerate("( ( (A 0 2) (B 0 2) (C 0 2) (D 0 2) ) ( (_1 lex_greater_than (A B) (C D)) ) )"))
        CHECK(((s.at("A") > s.at("C")) || (s.at("A") == s.at("C") && s.at("B") > s.at("D"))));
    // (A B) <=lex (C D): A < C, or A == C and B <= D.
    for (const auto & s : enumerate("( ( (A 0 2) (B 0 2) (C 0 2) (D 0 2) ) ( (_1 lex_less_equal (A B) (C D)) ) )"))
        CHECK(((s.at("A") < s.at("C")) || (s.at("A") == s.at("C") && s.at("B") <= s.at("D"))));
}

TEST_CASE("read_scp: a half-reified lex comparison enumerates correctly")
{
    // Z == 1  =>  (A B) >lex (C D) (a half reification: Z == 0 leaves it free).
    for (const auto & s : enumerate("( ( (Z 0 1) (A 0 1) (B 0 1) (C 0 1) (D 0 1) ) ( (_1 lex_greater_than_if (Z = 1) (A B) (C D)) ) )"))
        if (s.at("Z") == 1)
            CHECK(((s.at("A") > s.at("C")) || (s.at("A") == s.at("C") && s.at("B") > s.at("D"))));
}

TEST_CASE("read_scp: a fully-reified lex comparison enumerates correctly")
{
    // Z == 1  iff  (A B) <=lex (C D).
    for (const auto & s : enumerate("( ( (Z 0 1) (A 0 1) (B 0 1) (C 0 1) (D 0 1) ) ( (_1 lex_less_equal_iff (Z = 1) (A B) (C D)) ) )")) {
        bool le = (s.at("A") < s.at("C")) || (s.at("A") == s.at("C") && s.at("B") <= s.at("D"));
        CHECK((s.at("Z") == 1) == le);
    }
}

TEST_CASE("read_scp: global cardinality enumerates correctly")
{
    // CA counts the 0s among X, Y, Z; CB counts the 1s.
    for (const auto & s : enumerate("( ( (X 0 2) (Y 0 2) (Z 0 2) (CA 0 3) (CB 0 3) ) ( (_1 boundsglobalcardinality (X Y Z) (0 1) (CA CB)) ) )")) {
        CHECK(s.at("CA") == (s.at("X") == 0) + (s.at("Y") == 0) + (s.at("Z") == 0));
        CHECK(s.at("CB") == (s.at("X") == 1) + (s.at("Y") == 1) + (s.at("Z") == 1));
    }
    // The closed form additionally confines every variable to a cover value, so
    // the value 2 is excluded (the gac keyword selects the GAC propagator; the
    // solution set is the same).
    for (const auto & s : enumerate("( ( (X 0 2) (Y 0 2) (Z 0 2) (CA 0 3) (CB 0 3) ) ( (_1 gacglobalcardinalityclosed (X Y Z) (0 1) (CA CB)) ) )")) {
        CHECK((s.at("X") == 0 || s.at("X") == 1));
        CHECK(s.at("CA") + s.at("CB") == 3);
    }
}

TEST_CASE("read_scp: in with a mix of integer and variable values")
{
    // V in {0, 3} (constants) or = W (a variable).
    auto solutions = enumerate(R"(
        (
            ( (V 0 5) (W 0 5) )
            ( (_1 in (0 3 W) V) )
        ))");

    for (const auto & s : solutions)
        CHECK((s.at("V") == 0 || s.at("V") == 3 || s.at("V") == s.at("W")));
    // Every (V, W) with V in {0,3} (6 W values each) plus V == W (the rest).
    CHECK(! solutions.empty());
}

TEST_CASE("read_scp: comparisons enumerate correctly")
{
    for (const auto & s : enumerate("( ( (X 0 2) (Y 0 2) ) ( (_1 less_than X Y) ) )"))
        CHECK(s.at("X") < s.at("Y"));
    for (const auto & s : enumerate("( ( (X 0 2) (Y 0 2) ) ( (_1 less_equal X Y) ) )"))
        CHECK(s.at("X") <= s.at("Y"));
}

TEST_CASE("read_scp: a fully-reified comparison enumerates correctly")
{
    // C == 1  iff  X <= Y.
    for (const auto & s : enumerate("( ( (X 0 2) (Y 0 2) (C 0 1) ) ( (_1 less_equal_iff (C = 1) X Y) ) )"))
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
    for (const auto & s : enumerate("( ( (X 0 3) (Y 0 3) ) ( (_1 lin_equals (1 X 1 Y) 3) ) )"))
        CHECK(s.at("X") + s.at("Y") == 3);
    // X - Y <= 1
    for (const auto & s : enumerate("( ( (X 0 3) (Y 0 3) ) ( (_1 lin_less_equal (1 X -1 Y) 1) ) )"))
        CHECK(s.at("X") - s.at("Y") <= 1);
    // X + Y != 2
    for (const auto & s : enumerate("( ( (X 0 2) (Y 0 2) ) ( (_1 lin_not_equals (1 X 1 Y) 2) ) )"))
        CHECK(s.at("X") + s.at("Y") != 2);
}

TEST_CASE("read_scp: a reified linear constraint enumerates correctly")
{
    // C == 1  iff  X + Y == 3.
    for (const auto & s : enumerate("( ( (X 0 3) (Y 0 3) (C 0 1) ) ( (_1 lin_equals_iff (C = 1) (1 X 1 Y) 3) ) )"))
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

TEST_CASE("read_scp: equals and not_equals enumerate correctly")
{
    for (const auto & s : enumerate("( ( (X 0 2) (Y 0 2) ) ( (_1 equals X Y) ) )"))
        CHECK(s.at("X") == s.at("Y"));
    for (const auto & s : enumerate("( ( (X 0 2) (Y 0 2) ) ( (_1 not_equals X Y) ) )"))
        CHECK(s.at("X") != s.at("Y"));
    // not_equals against a constant, the way crystal_maze uses it.
    for (const auto & s : enumerate("( ( (X -2 2) ) ( (_1 not_equals X 0) ) )"))
        CHECK(s.at("X") != 0);
}

TEST_CASE("read_scp: a reified equals enumerates correctly")
{
    // C == 1  iff  X == Y.
    for (const auto & s : enumerate("( ( (X 0 2) (Y 0 2) (C 0 1) ) ( (_1 equals_iff (C = 1) X Y) ) )"))
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
    for (const auto & s : enumerate("( ( (R 0 15) (I 0 3) ) ( (_1 element (5 7 9 11) (I 0) R) ) )"))
        CHECK(s.at("R") == arr[s.at("I")]);

    // With an offset of 1, I in 1..4 selects arr[I - 1].
    for (const auto & s : enumerate("( ( (R 0 15) (I 1 4) ) ( (_1 element (5 7 9 11) (I 1) R) ) )"))
        CHECK(s.at("R") == arr[s.at("I") - 1]);

    // A variable array: R = (I == 0 ? A : B).
    for (const auto & s : enumerate("( ( (A 0 2) (B 0 2) (R 0 2) (I 0 1) ) ( (_1 element (A B) (I 0) R) ) )"))
        CHECK(s.at("R") == (s.at("I") == 0 ? s.at("A") : s.at("B")));
}

TEST_CASE("read_scp: count enumerates correctly")
{
    // K = #{ v in (A, B, C) : v == V }.
    for (const auto & s : enumerate("( ( (A 0 2) (B 0 2) (C 0 2) (V 0 2) (K 0 3) ) ( (_1 count (A B C) V K) ) )")) {
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
    for (const auto & s : enumerate("( ( (X0 0 1) (X1 0 1) (X2 0 1) ) ( (_1 regular (X0 X1 X2) 2 ( ((0 0) (1 1)) ((0 1) (1 0)) ) (0)) ) )"))
        CHECK((s.at("X0") + s.at("X1") + s.at("X2")) % 2 == 0);
}

TEST_CASE("read_scp: disjunctive enumerates correctly")
{
    // Two length-2 tasks in 0..3 must not overlap, so their starts differ by at
    // least 2. The strict keyword variant builds the same solution set for
    // positive lengths.
    for (const auto & s : enumerate("( ( (S0 0 3) (S1 0 3) ) ( (_1 disjunctive (S0 S1) (2 2)) ) )")) {
        auto d = s.at("S0") - s.at("S1");
        CHECK((d >= 2 || d <= -2));
    }
    for (const auto & s : enumerate("( ( (S0 0 3) (S1 0 3) ) ( (_1 disjunctive_strict (S0 S1) (2 2)) ) )")) {
        auto d = s.at("S0") - s.at("S1");
        CHECK((d >= 2 || d <= -2));
    }
    // Variable durations are allowed too: the length list may name variables.
    for (const auto & s : enumerate("( ( (S0 0 4) (S1 0 4) (D 1 2) ) ( (_1 disjunctive (S0 S1) (D D)) ) )")) {
        auto d = s.at("S0") - s.at("S1");
        CHECK((d >= s.at("D") || d <= -s.at("D")));
    }
}

TEST_CASE("read_scp: disjunctive2d enumerates correctly")
{
    // Two 2x2 rectangles in a 0..3 x 0..3 grid must not overlap, so they are
    // separated in x or in y.
    for (const auto & s : enumerate("( ( (X0 0 3) (X1 0 3) (Y0 0 3) (Y1 0 3) ) ( (_1 disjunctive2d (X0 X1) (Y0 Y1) (2 2) (2 2)) ) )")) {
        auto dx = s.at("X0") - s.at("X1");
        auto dy = s.at("Y0") - s.at("Y1");
        CHECK((dx >= 2 || dx <= -2 || dy >= 2 || dy <= -2));
    }
}

TEST_CASE("read_scp: regular, disjunctive and disjunctive2d survive write -> read -> write unchanged")
{
    Problem original;
    auto x0 = original.create_integer_variable(0_i, 1_i, "X0");
    auto x1 = original.create_integer_variable(0_i, 1_i, "X1");
    auto s0 = original.create_integer_variable(0_i, 3_i, "S0");
    auto s1 = original.create_integer_variable(0_i, 3_i, "S1");
    auto y0 = original.create_integer_variable(0_i, 3_i, "Y0");
    auto y1 = original.create_integer_variable(0_i, 3_i, "Y1");
    original.post(Regular{std::vector<IntegerVariableID>{x0, x1}, 2,
        std::vector<std::unordered_map<Integer, long>>{{{0_i, 0}, {1_i, 1}}, {{0_i, 1}, {1_i, 0}}},
        std::vector<long>{0}});
    original.post(Disjunctive{std::vector<IntegerVariableID>{s0, s1}, std::vector<Integer>{2_i, 2_i}});        // strict -> disjunctive_strict
    original.post(Disjunctive{std::vector<IntegerVariableID>{s0, s1}, std::vector<Integer>{2_i, 2_i}, false}); // non-strict -> disjunctive
    original.post(Disjunctive2D{std::vector<IntegerVariableID>{s0, s1}, std::vector<IntegerVariableID>{y0, y1},
        std::vector<Integer>{2_i, 2_i}, std::vector<Integer>{2_i, 2_i}, false});
    auto scp_a = prove_to_scp(original, "scp_reader_regdisj_a");

    Problem rebuilt;
    read_scp(rebuilt, scp_a);
    auto scp_b = prove_to_scp(rebuilt, "scp_reader_regdisj_b");

    CHECK(scp_a == scp_b);
    CHECK_FALSE(scp_a.empty());
}

TEST_CASE("read_scp: a constant integer can stand in for a variable anywhere")
{
    // An abs operand that is a constant: Y = |3|.
    CHECK(enumerate("( ( (Y 0 5) ) ( (_1 abs 3 Y) ) )") ==
        set<map<string, long long>>{{{"Y", 3}}});

    // A constant member of all_different: A, 1, B all distinct, so A,B in {0,2}.
    auto all_diff = enumerate("( ( (A 0 2) (B 0 2) ) ( (_1 all_different (A 1 B)) ) )");
    CHECK(all_diff == set<map<string, long long>>{{{"A", 0}, {"B", 2}}, {{"A", 2}, {"B", 0}}});
}

TEST_CASE("read_scp: constraint labels and variable names round-trip via the map")
{
    Problem problem;
    auto variables = read_scp(problem, "( ( (X 0 1) (Y 0 1) ) ( (_1 abs X Y) ) )");
    CHECK(variables.size() == 2);
    CHECK(variables.contains("X"));
    CHECK(variables.contains("Y"));
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

TEST_CASE("read_scp: an out-of-order auto-number is rejected, not silently relabelled")
{
    // A single constraint labelled _2 would auto-number to _1 on re-post, so
    // post_autonumbered rejects the mismatch instead of quietly changing it.
    CHECK_THROWS_AS(enumerate("( ( (X 0 1) (Y 0 1) ) ( (_2 abs X Y) ) )"), NamingError);
}

TEST_CASE("read_scp: unsupported and malformed input throws")
{
    CHECK_THROWS_AS(enumerate("( ( (X 0 1) ) ( (_1 frobnicate X) ) )"), ScpReadError);
    CHECK_THROWS_AS(enumerate("( ( (X 0 1) ) )"), ScpReadError);        // not (vars constraints)
    CHECK_THROWS_AS(enumerate("( ( (X 0) ) ( ) )"), ScpReadError);      // bad var decl
    CHECK_THROWS_AS(enumerate("( ( (X zero 1) ) ( ) )"), ScpReadError); // non-integer bound
    CHECK_THROWS_AS(enumerate("not an s-expr ("), innards::SExprParseError);
}
