#include <gcs/constraints/comparison.hh>
#include <gcs/expression.hh>
#include <gcs/presolvers/auto_table.hh>
#include <gcs/problem.hh>
#include <gcs/solve.cc>

#include <catch2/catch_test_macros.hpp>

#include <cstdlib>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::vector;

TEST_CASE("Solve unsat")
{
    Problem p;
    auto v = p.create_integer_variable(0_i, 100_i);
    p.post(WeightedSum{} + 1_i * v >= 200_i);

    bool found_solution = false;
    solve(
        p, [&](const CurrentState &) -> bool {
            found_solution = true;
            return false;
        },
        ProofOptions{"solve_test"});

    CHECK(! found_solution);
    CHECK(system("$HOME/.cargo/bin/veripb solve_test.opb solve_test.pbp") == EXIT_SUCCESS);
}

TEST_CASE("Solve unsat by model optimisation")
{
    Problem p;
    auto v = p.create_integer_variable(0_i, 100_i);
    p.post(LessThan{1_c, 0_c});
    p.maximise(v);

    bool found_solution = false;
    solve(
        p, [&](const CurrentState &) -> bool {
            found_solution = true;
            return false;
        },
        ProofOptions{"solve_test"});

    CHECK(! found_solution);
    CHECK(system("$HOME/.cargo/bin/veripb solve_test.opb solve_test.pbp") == EXIT_SUCCESS);
}

TEST_CASE("Solve unsat optimisation presolving")
{
    Problem p;
    auto v = p.create_integer_variable(0_i, 100_i);
    p.post(WeightedSum{} + 1_i * v >= 200_i);
    p.add_presolver(AutoTable{vector<IntegerVariableID>{v}});

    bool found_solution = false;
    solve(
        p, [&](const CurrentState &) -> bool {
            found_solution = true;
            return false;
        },
        ProofOptions{"solve_test"});

    CHECK(! found_solution);
    CHECK(system("$HOME/.cargo/bin/veripb solve_test.opb solve_test.pbp") == EXIT_SUCCESS);
}
