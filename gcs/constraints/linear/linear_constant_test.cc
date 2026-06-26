#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <set>
#include <string>
#include <tuple>

using std::cerr;
using std::flush;
using std::make_optional;
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
        auto proof_name = proofs ? make_optional("linear_constant_test") : nullopt;
        solve_for_tests(p, proof_name, actual, tuple{x});
        check_results(proof_name, expected, actual);
    }
}

auto main(int, char *[]) -> int
{
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
    }

    return EXIT_SUCCESS;
}
