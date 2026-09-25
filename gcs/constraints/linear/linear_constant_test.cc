#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/innards/literal.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <set>
#include <string>
#include <tuple>
#include <utility>

using std::cerr;
using std::flush;
using std::make_optional;
using std::move;
using std::nullopt;
using std::set;
using std::string;
using std::tuple;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::println;
#else
using fmt::println;
#endif

using namespace gcs;
using namespace gcs::test_innards;

// Regression test for the empty-sum-with-constant bug: a linear (in)equality
// all of whose terms are constants tidies down to no variable terms, with the
// constant part folded into `modifier`. The fixed-condition shortcut must then
// compare the empty sum (0) against `value + modifier`, i.e. it holds iff
// `modifier == -value`. The old code compared against `value` directly, which
// reported the tautology 1*1 == 1 (from e.g. bool_lin_eq([1],[true],1)) as a
// spurious contradiction -- a wrong UNSAT that VeriPB correctly rejected.

namespace
{
    // CI runs this test in both propagation modes via GCS_LINEAR_INCREMENTAL_THRESHOLD;
    // tag the proof file name so the two runs don't clobber each other under parallel ctest.
    auto threshold_proof_suffix() -> string
    {
        if (const char * e = std::getenv("GCS_LINEAR_INCREMENTAL_THRESHOLD"))
            return string{"_t"} + e;
        return {};
    }

    // Post `cons` over an otherwise-free x in 0..2; if the constant constraint is
    // satisfiable the free x yields {0,1,2}, otherwise no solutions at all.
    template <typename PostConstraint_>
    auto run_constant_linear_test(bool proofs, const string & label, bool satisfiable, const PostConstraint_ & post) -> void
    {
        println(cerr, "linear constant: {}{}", label, proofs ? " with proofs:" : ":");
        cerr << flush;

        set<tuple<int>> expected;
        if (satisfiable)
            for (int x = 0; x <= 2; ++x)
                expected.emplace(x);

        Problem p;
        auto x = p.create_integer_variable(0_i, 2_i);
        post(p);

        set<tuple<int>> actual;
        auto proof_name = proofs ? make_optional("linear_constant_test" + threshold_proof_suffix()) : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{x});
        check_results(proof_name, expected, actual);
    }

    // A reified equality or disequality whose condition is a constant literal
    // (issue #1033), over x, y in 0..2 against x + y == 3: the solutions are all
    // nine pairs, the two where the sum is 3, or the seven where it is not. What a
    // constant condition means depends on the form: true enforces If's equality
    // and NotIf's disequality, false releases either half-reified form, and an
    // Iff enforces the negated relation when false.
    enum class Expect
    {
        All,
        SumIs3,
        SumIsNot3
    };

    template <typename Constraint_>
    auto run_constant_condition_test(bool proofs, const string & label, innards::Literal cond, Expect expect, bool tabulated) -> void
    {
        println(cerr, "linear constant condition: {}{}{}", label, tabulated ? " tabulated" : "", proofs ? " with proofs:" : ":");
        cerr << flush;

        set<tuple<int, int>> expected;
        for (int x = 0; x <= 2; ++x)
            for (int y = 0; y <= 2; ++y)
                if (expect == Expect::All || (expect == Expect::SumIs3) == (x + y == 3))
                    expected.emplace(x, y);

        Problem p;
        auto x = p.create_integer_variable(0_i, 2_i);
        auto y = p.create_integer_variable(0_i, 2_i);
        auto c = Constraint_{WeightedSum{} + 1_i * x + 1_i * y, 3_i, cond};
        if (tabulated)
            c.with_consistency(consistency::Tabulated{});
        p.post(move(c));

        set<tuple<int, int>> actual;
        auto proof_name = proofs ? make_optional("linear_constant_test" + threshold_proof_suffix()) : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{x, y});
        check_results(proof_name, expected, actual);
    }

    // A half-reified form released by a false constant condition installs
    // nothing, whatever the consistency level: under Tabulated it used to build
    // and run a table over every tuple (issue #1103). The answers were right
    // either way, so only the propagator count can see it.
    template <typename Constraint_>
    auto run_released_installs_nothing_test(const string & label, bool tabulated) -> void
    {
        println(cerr, "linear released form installs nothing: {}{}", label, tabulated ? " tabulated" : "");
        cerr << flush;

        Problem p;
        auto x = p.create_integer_variable(0_i, 2_i);
        auto y = p.create_integer_variable(0_i, 2_i);
        auto c = Constraint_{WeightedSum{} + 1_i * x + 1_i * y, 3_i, innards::FalseLiteral{}};
        if (tabulated)
            c.with_consistency(consistency::Tabulated{});
        p.post(move(c));

        auto stats = solve(p, [](const CurrentState &) -> bool { return true; });
        if (stats.solutions != 9 || stats.n_propagators != 0 || stats.propagations != 0) {
            println(cerr, "expected 9 solutions from no propagators, got {} solutions, {} propagators, {} propagations", stats.solutions,
                stats.n_propagators, stats.propagations);
            std::exit(EXIT_FAILURE);
        }
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    for (bool proofs : {false, true}) {
        if (proofs && ! can_run_veripb())
            continue;

        // LinearEquality (condition definitely true): empty sum holds iff value + modifier == 0.
        run_constant_linear_test(proofs, "1*1 == 1 (tautology)", true, [](Problem & p) { p.post(LinearEquality{WeightedSum{} + 1_i * 1_c, 1_i}); });
        run_constant_linear_test(
            proofs, "1*1 == 2 (contradiction)", false, [](Problem & p) { p.post(LinearEquality{WeightedSum{} + 1_i * 1_c, 2_i}); });
        run_constant_linear_test(
            proofs, "2*3 == 6 (tautology, coeff != 1)", true, [](Problem & p) { p.post(LinearEquality{WeightedSum{} + 2_i * 3_c, 6_i}); });
        run_constant_linear_test(
            proofs, "2*3 == 5 (contradiction, coeff != 1)", false, [](Problem & p) { p.post(LinearEquality{WeightedSum{} + 2_i * 3_c, 5_i}); });

        // LinearNotEquals (condition definitely false): empty sum is violated iff it would hold.
        run_constant_linear_test(
            proofs, "1*1 != 1 (contradiction)", false, [](Problem & p) { p.post(LinearNotEquals{WeightedSum{} + 1_i * 1_c, 1_i}); });
        run_constant_linear_test(proofs, "1*1 != 2 (tautology)", true, [](Problem & p) { p.post(LinearNotEquals{WeightedSum{} + 1_i * 1_c, 2_i}); });

        // Mixed: a real variable term plus a constant term leaves a non-empty sum,
        // so the constant is folded into the modifier but the normal propagation path runs.
        run_constant_linear_test(proofs, "y(=5) + 3 == 8 (tautology, constant folded)", true, [](Problem & p) {
            auto y = p.create_integer_variable(5_i, 5_i, "y");
            p.post(LinearEquality{WeightedSum{} + 1_i * y + 1_i * 3_c, 8_i});
        });

        // Negative constant terms / RHS: the empty-sum shortcut compares the
        // folded constant against the RHS with everything crossing zero, so a
        // sign error in the fold surfaces only here. (Constant terms are formed
        // with a negative coefficient, since `_c` literals are non-negative.)
        run_constant_linear_test(
            proofs, "-1*1 == -1 (tautology)", true, [](Problem & p) { p.post(LinearEquality{WeightedSum{} + -1_i * 1_c, -1_i}); });
        run_constant_linear_test(
            proofs, "-1*1 == 0 (contradiction)", false, [](Problem & p) { p.post(LinearEquality{WeightedSum{} + -1_i * 1_c, 0_i}); });
        run_constant_linear_test(
            proofs, "-2*3 == -6 (tautology, coeff != 1)", true, [](Problem & p) { p.post(LinearEquality{WeightedSum{} + -2_i * 3_c, -6_i}); });
        run_constant_linear_test(
            proofs, "-2*3 == -5 (contradiction, coeff != 1)", false, [](Problem & p) { p.post(LinearEquality{WeightedSum{} + -2_i * 3_c, -5_i}); });

        // LinearNotEquals with negatives.
        run_constant_linear_test(
            proofs, "-1*1 != -1 (contradiction)", false, [](Problem & p) { p.post(LinearNotEquals{WeightedSum{} + -1_i * 1_c, -1_i}); });
        run_constant_linear_test(
            proofs, "-1*1 != 0 (tautology)", true, [](Problem & p) { p.post(LinearNotEquals{WeightedSum{} + -1_i * 1_c, 0_i}); });

        // Mixed with a negative variable value and a negative folded constant:
        // y(=-5) + (-3) == -8 leaves a non-empty sum whose modifier is negative.
        run_constant_linear_test(proofs, "y(=-5) + (-3) == -8 (tautology, constant folded)", true, [](Problem & p) {
            auto y = p.create_integer_variable(-5_i, -5_i, "y");
            p.post(LinearEquality{WeightedSum{} + 1_i * y + -1_i * 3_c, -8_i});
        });

        for (bool tabulated : {false, true}) {
            run_constant_condition_test<LinearEqualityIf>(proofs, "x + y == 3 if true", innards::TrueLiteral{}, Expect::SumIs3, tabulated);
            run_constant_condition_test<LinearEqualityIf>(proofs, "x + y == 3 if false", innards::FalseLiteral{}, Expect::All, tabulated);
            run_constant_condition_test<LinearEqualityIff>(proofs, "x + y == 3 iff true", innards::TrueLiteral{}, Expect::SumIs3, tabulated);
            run_constant_condition_test<LinearEqualityIff>(proofs, "x + y == 3 iff false", innards::FalseLiteral{}, Expect::SumIsNot3, tabulated);
            run_constant_condition_test<LinearNotEqualsIf>(proofs, "x + y != 3 if true", innards::TrueLiteral{}, Expect::SumIsNot3, tabulated);
            run_constant_condition_test<LinearNotEqualsIf>(proofs, "x + y != 3 if false", innards::FalseLiteral{}, Expect::All, tabulated);
            run_constant_condition_test<LinearNotEqualsIff>(proofs, "x + y != 3 iff true", innards::TrueLiteral{}, Expect::SumIsNot3, tabulated);
            run_constant_condition_test<LinearNotEqualsIff>(proofs, "x + y != 3 iff false", innards::FalseLiteral{}, Expect::SumIs3, tabulated);
        }
    }

    for (bool tabulated : {false, true}) {
        run_released_installs_nothing_test<LinearEqualityIf>("x + y == 3 if false", tabulated);
        run_released_installs_nothing_test<LinearNotEqualsIf>("x + y != 3 if false", tabulated);
    }

    return EXIT_SUCCESS;
}
