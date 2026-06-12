#include <gcs/constraints/equals.hh>
#include <gcs/current_state.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <vector>

using namespace gcs;
using std::vector;

// Witness W5 (see dev_docs/range_literals_spec.md): root covering / wipeout. Every
// cell of x's partition is excluded by interval conclusions (x loses [0,2] and
// [5,7] through Equals(x,y), then [3,4] through Equals(x,w), wiping the domain at
// the root), and the final contradiction must be reachable by unit propagation at
// the flag level: the root covering's pieces are falsified through the coverings,
// without descending to the bits. The instance is UNSAT with no search at all, so
// the only thing VeriPB has to check is precisely that wipeout derivation.
auto main() -> int
{
    Problem p;
    auto x = p.create_integer_variable(0_i, 7_i, "x");
    auto y = p.create_integer_variable(vector{3_i, 4_i}, "y");
    auto w = p.create_integer_variable(vector{0_i, 1_i, 2_i, 5_i, 6_i, 7_i}, "w");

    p.post(Equals{x, y});
    p.post(Equals{x, w});

    solve(
        p, [](const CurrentState &) -> bool { return true; },
        ProofOptions{"range_witness_w5_test"});

    return 0;
}
