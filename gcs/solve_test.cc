#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/element.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/plus.hh>
#include <gcs/expression.hh>
#include <gcs/presolvers/auto_table.hh>
#include <gcs/problem.hh>
#include <gcs/solve.cc>

#include <catch2/catch_test_macros.hpp>

#include <cstdlib>
#include <optional>
#include <vector>

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::test_innards;

using std::nullopt;
using std::optional;
using std::vector;

TEST_CASE("Solve unsat")
{
    Problem p;
    auto v = p.create_integer_variable(0_i, 100_i);
    p.post(WeightedSum{} + 1_i * v >= 200_i);

    bool found_solution = false;
    solve(
        p,
        [&](const CurrentState &) -> bool {
            found_solution = true;
            return false;
        },
        ProofOptions{"solve_test"});

    CHECK(! found_solution);
    CHECK(run_veripb("solve_test.opb", "solve_test.pbp"));
}

TEST_CASE("Solve unsat by model optimisation")
{
    Problem p;
    auto v = p.create_integer_variable(0_i, 100_i);
    p.post(LessThan{1_c, 0_c});
    p.maximise(v);

    bool found_solution = false;
    solve(
        p,
        [&](const CurrentState &) -> bool {
            found_solution = true;
            return false;
        },
        ProofOptions{"solve_test"});

    CHECK(! found_solution);
    CHECK(run_veripb("solve_test.opb", "solve_test.pbp"));
}

// Four variables over three values, pairwise different: unsatisfiable, and
// posted as weak pairwise NotEquals (no Hall pruning) so search must branch and
// hit conflicts rather than wiping out at the root. A luby(1) schedule then
// restarts after almost every conflict, so the search only terminates because
// the growing cutoff eventually exceeds the whole tree --- exercising the
// restart loop and that the proof stays balanced across many restarts.
TEST_CASE("Solve unsat with restarts")
{
    Problem p;
    vector<IntegerVariableID> xs;
    for (int i = 0; i < 4; ++i)
        xs.push_back(p.create_integer_variable(0_i, 2_i));
    for (unsigned i = 0; i < xs.size(); ++i)
        for (unsigned j = i + 1; j < xs.size(); ++j)
            p.post(NotEquals{xs[i], xs[j]});

    bool found_solution = false;
    auto stats = solve_with(p,
        SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                           found_solution = true;
                           return false;
                       },
            .restarts = RestartSchedule::luby(1)},
        ProofOptions{"solve_test"});

    CHECK(! found_solution);
    CHECK(stats.restarts > 0);
    CHECK(run_veripb("solve_test.opb", "solve_test.pbp"));
}

// Optimisation with restarts: the incumbent bound persists across restarts, so
// each pass only finds strictly better solutions and the final pass proves
// optimality. Objective-bound dead-ends count as conflicts, so a luby(1)
// schedule restarts here too.
TEST_CASE("Optimise with restarts")
{
    Problem p;
    auto x = p.create_integer_variable(0_i, 2_i);
    auto y = p.create_integer_variable(0_i, 2_i);
    auto z = p.create_integer_variable(0_i, 2_i);
    p.post(NotEquals{x, y});
    p.post(NotEquals{x, z});
    p.post(NotEquals{y, z});
    p.maximise(x);

    optional<Integer> best = nullopt;
    auto stats = solve_with(p,
        SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
                           best = s(x);
                           return true;
                       },
            .restarts = RestartSchedule::luby(1)},
        ProofOptions{"solve_test"});

    CHECK(best == optional<Integer>{2_i});
    CHECK(stats.restarts > 0);
    CHECK(run_veripb("solve_test.opb", "solve_test.pbp"));
}

// Without nogoods, restarts cannot soundly enumerate: a callback that keeps
// going after a solution, with no objective, is the one unsupported combination,
// and is rejected rather than allowed to miscount.
TEST_CASE("Restarts refuse to enumerate all solutions")
{
    Problem p;
    auto x = p.create_integer_variable(0_i, 2_i);
    auto y = p.create_integer_variable(0_i, 2_i);
    p.post(NotEquals{x, y});

    CHECK_THROWS_AS(
        solve_with(p, SolveCallbacks{.solution = [](const CurrentState &) -> bool { return true; }, .restarts = RestartSchedule::luby(1)}),
        UnimplementedException);
}

// An unsatisfiable Langford-pairing instance (size 5): rich enough that
// AllDifferent and Element prune at the root, so the root node emits
// guess-independent propagation that later restart passes do not re-derive.
// This guards the fix that keeps that root reasoning (proof level 1) across
// restarts; the NotEquals cases above have too little root propagation to
// exercise it. The luby scale is chosen so a couple of restarts fire before the
// growing cutoff exhausts the tree.
TEST_CASE("Solve unsat with restarts and root propagation")
{
    Problem p;
    const int k = 5;
    vector<IntegerVariableID> position, solution;
    for (int i = 0; i < 2 * k; ++i) {
        position.emplace_back(p.create_integer_variable(0_i, Integer{2 * k - 1}));
        solution.emplace_back(p.create_integer_variable(1_i, Integer{k}));
    }
    p.post(AllDifferent{position});
    for (int i = 0; i < k; ++i) {
        auto i_var = p.create_integer_variable(Integer{i + 1}, Integer{i + 1});
        p.post(Element{i_var, position[i], &solution});
        p.post(Element{i_var, position[i + k], &solution});
        p.post(Plus{position[i + k], constant_variable(Integer{i + 2}), position[i]}.with_consistency(consistency::Tabulated{}));
    }

    bool found_solution = false;
    auto stats = solve_with(p,
        SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                           found_solution = true;
                           return false;
                       },
            .restarts = RestartSchedule::luby(10)},
        ProofOptions{"solve_test"});

    CHECK(! found_solution);
    CHECK(stats.restarts > 0);
    CHECK(run_veripb("solve_test.opb", "solve_test.pbp"));
}

TEST_CASE("Solve unsat optimisation presolving")
{
    Problem p;
    auto v = p.create_integer_variable(0_i, 100_i);
    p.post(WeightedSum{} + 1_i * v >= 200_i);
    p.add_presolver(AutoTable{vector<IntegerVariableID>{v}});

    bool found_solution = false;
    solve(
        p,
        [&](const CurrentState &) -> bool {
            found_solution = true;
            return false;
        },
        ProofOptions{"solve_test"});

    CHECK(! found_solution);
    CHECK(run_veripb("solve_test.opb", "solve_test.pbp"));
}
