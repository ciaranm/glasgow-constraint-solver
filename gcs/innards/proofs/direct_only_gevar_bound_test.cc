#include <gcs/constraints/linear.hh>
#include <gcs/current_state.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

using namespace gcs;

// Regression for issue #554: a {0,1} DirectOnly variable's `>= 1` order atom
// must be a genuine reified ge-atom line, not the bare bit literal.
//
// A weighted `pol` that substitutes a lower-bound atom (justify_linear_bounds,
// for the objective-bound derivation here) adds `coeff * (x >= L)`'s defining
// row to cancel the base constraint's `coeff * x` term, leaving `coeff * ~g`
// and `coeff * L` of degree behind. If `x >= 1` is aliased to the encoding bit
// b0 (the old {0,1} encoding), `need_pol_item_defining_literal` returns a bare
// literal, `add_for_literal` pushes the degree-0 axiom `b0 coeff *`, and that
// axiom CANCELS the base's own `~b0` term outright -- the derived bound comes
// out `coeff` short and the objective-bound RUP fails to verify.
//
// The failure only surfaces when at least two wide, only-lower-bounded bits
// variables share the objective sum: with one, VeriPB's bitwise unit
// propagation binary-searches the true bound back out of the raw constraint;
// with two, every constraint's slack spans the other variable's full range, no
// bit propagates, and the short bound stands. So: x forced to 1 (coeff 200),
// z1, z2 in [0, 1023] lower-bounded to 300 (slack 723 > 512, bit-opaque),
// obj = 200x + z1 + z2. Root propagation infers obj >= 800; the buggy pol
// derives only obj >= 600, and veripb rejects the bound RUP. (Distilled from
// the mznc2023 unit-commitment instance, whose objective sum has 59 such
// terms.) The solve is trivially satisfiable; the proof obligation is the whole
// point, so run under run_test_and_verify.bash.
auto main() -> int
{
    Problem p;
    auto x = p.create_integer_variable(0_i, 1_i, "x");
    auto z1 = p.create_integer_variable(0_i, 1023_i, "z1");
    auto z2 = p.create_integer_variable(0_i, 1023_i, "z2");
    auto obj = p.create_integer_variable(0_i, 4095_i, "obj");

    p.post(LinearGreaterThanEqual{WeightedSum{} + 1_i * x, 1_i});
    p.post(LinearGreaterThanEqual{WeightedSum{} + 1_i * z1, 300_i});
    p.post(LinearGreaterThanEqual{WeightedSum{} + 1_i * z2, 300_i});
    p.post(LinearEquality{WeightedSum{} + 200_i * x + 1_i * z1 + 1_i * z2 + -1_i * obj, 0_i});

    p.minimise(obj);

    solve_with(p, SolveCallbacks{.solution = [](const CurrentState &) -> bool { return true; }}, ProofOptions{"direct_only_gevar_bound_test"});

    return 0;
}
