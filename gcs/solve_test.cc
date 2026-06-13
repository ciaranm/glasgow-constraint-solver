#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/arithmetic.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/element.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/expression.hh>
#include <gcs/presolvers/auto_table.hh>
#include <gcs/problem.hh>
#include <gcs/solve.cc>

#include <catch2/catch_test_macros.hpp>

#include <cstdlib>
#include <optional>
#include <set>
#include <tuple>
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
        p, [&](const CurrentState &) -> bool {
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
        p, [&](const CurrentState &) -> bool {
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
    auto stats = solve_with(
        p,
        SolveCallbacks{
            .solution = [&](const CurrentState &) -> bool { found_solution = true; return false; },
            .restarts = RestartSchedule::luby(1)},
        ProofOptions{"solve_test"});

    CHECK(! found_solution);
    CHECK(stats.restarts > 0);
    // Restarts learn nogoods from the refuted regions, and the proof verifies
    // those learned clauses (an unsound one would fail RUP).
    CHECK(stats.learned_nogoods > 0);
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
    auto stats = solve_with(
        p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool { best = s(x); return true; },
            .restarts = RestartSchedule::luby(1)},
        ProofOptions{"solve_test"});

    CHECK(best == optional<Integer>{2_i});
    CHECK(stats.restarts > 0);
    CHECK(run_veripb("solve_test.opb", "solve_test.pbp"));
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
        p.post(PlusGAC{position[i + k], constant_variable(Integer{i + 2}), position[i]});
    }

    bool found_solution = false;
    auto stats = solve_with(
        p,
        SolveCallbacks{
            .solution = [&](const CurrentState &) -> bool { found_solution = true; return false; },
            .restarts = RestartSchedule::luby(10)},
        ProofOptions{"solve_test"});

    CHECK(! found_solution);
    CHECK(stats.restarts > 0);
    CHECK(run_veripb("solve_test.opb", "solve_test.pbp"));
}

// Enumerate every solution while restarting. b, c, d are a pairwise-distinct
// triangle (a permutation of {1,2,3}) and a (domain 1..4) must differ from all
// three, forcing a = 4 --- so there are six solutions. But a branched to 1/2/3
// early leaves b, c, d needing three distinct values in the two that remain: a
// dead end. Random branching hits those, so a luby(1) schedule restarts
// part-way through enumeration. Each solution must still be reported exactly
// once: the nld nogoods, sound because solx excludes the solutions already
// found, stop a later pass re-entering an exhausted region. The proof must
// conclude a complete enumeration of six.
TEST_CASE("Enumerate all solutions with restarts")
{
    Problem p;
    auto a = p.create_integer_variable(1_i, 4_i);
    auto b = p.create_integer_variable(1_i, 3_i);
    auto c = p.create_integer_variable(1_i, 3_i);
    auto d = p.create_integer_variable(1_i, 3_i);
    p.post(NotEquals{a, b});
    p.post(NotEquals{a, c});
    p.post(NotEquals{a, d});
    p.post(NotEquals{b, c});
    p.post(NotEquals{b, d});
    p.post(NotEquals{c, d});

    std::set<std::tuple<int, int, int, int>> solutions;
    unsigned long long callbacks = 0;
    auto stats = solve_with(
        p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                ++callbacks;
                solutions.emplace(s(a).raw_value, s(b).raw_value, s(c).raw_value, s(d).raw_value);
                return true;
            },
            .branch = branch_with(variable_order::random(p, 1234), value_order::random_out(5678)),
            .restarts = RestartSchedule::luby(1)},
        ProofOptions{"solve_test"});

    CHECK(solutions.size() == 6);
    CHECK(callbacks == 6); // each solution reported exactly once, no re-counting
    CHECK(stats.solutions == 6);
    CHECK(stats.restarts > 0); // restarts actually fired during enumeration
    CHECK(stats.learned_nogoods > 0);
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
        p, [&](const CurrentState &) -> bool {
            found_solution = true;
            return false;
        },
        ProofOptions{"solve_test"});

    CHECK(! found_solution);
    CHECK(run_veripb("solve_test.opb", "solve_test.pbp"));
}
