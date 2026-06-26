#include <gcs/constraints/equals.hh>
#include <gcs/current_state.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

using namespace gcs;

// Stage-4 controlled check: a small enumeration solved with reject_random_interval
// branching, so backtrack clauses over interval-reject decisions get VeriPB-checked.
auto main() -> int
{
    Problem p;
    auto x = p.create_integer_variable(0_i, 4_i, "x");
    auto y = p.create_integer_variable(0_i, 4_i, "y");
    p.post(NotEquals{x, y});

    solve_with(p,
        SolveCallbacks{.solution = [](const CurrentState &) -> bool { return true; },
            .branch = branch_with(variable_order::random(p, 1), value_order::reject_random_interval(1))},
        ProofOptions{"range_branch_test"});

    return 0;
}
