#include <gcs/constraints/sort.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <optional>
#include <vector>

using namespace gcs;
using std::make_optional;
using std::nullopt;
using std::vector;

// Throwaway probe: x[i] in [0, i+1] (NOT fixed: lower bound 0), y in [0, N+1].
// At the root, the down-sweep matches y[j] to x[j] and tightens y[j] <= j+1 by
// the order statistic, with U = j+1. The count line Sum_k [x_k <= U] >= j+1
// grows to N, and the forced indices i<j have ub(x[i]) = i+1 STRICTLY below
// U = j+1 while x[i] is not fixed -- so the count RUP genuinely has to
// propagate [x_i <= U] from x_i <= i+1 through the order ladder (not constant-
// fold it, as a fixed x would). The root inferences are emitted before any
// search descent, so capping to one solution keeps the proof small while still
// exercising the big-count lines. Guards against the count being RUP only
// because the test counts are small / the literals are constants.
auto main(int argc, char *[]) -> int
{
    const int N = 20;
    Problem p;
    vector<IntegerVariableID> x, y;
    for (int i = 0; i < N; ++i)
        x.push_back(p.create_integer_variable(0_i, Integer{i + 1}));
    for (int j = 0; j < N; ++j)
        y.push_back(p.create_integer_variable(0_i, Integer{N + 1}));
    p.post(Sort{x, y});

    solve(
        p, [&](const CurrentState &) -> bool { return false; },
        make_optional<ProofOptions>("sort_count_probe"));

    return EXIT_SUCCESS;
}
