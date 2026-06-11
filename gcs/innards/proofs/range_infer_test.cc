#include <gcs/constraints/equals.hh>
#include <gcs/current_state.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <vector>

using namespace gcs;
using std::vector;

// Check for the single-line range inference. A plain Equals(x, y) where each side
// carries a contiguous hole, so the propagator removes the non-shared interval from
// each. This removal is a single ~[x in lo..hi] proof line, justified across the
// *unmodified* bit-sum equality by two bound-lemmas (each RUP via Theorem 2.9 /
// Justification Procedure 3.2) plus an RUP conclusion -- demonstrating that an
// interval of infer_not_equal can be collapsed into a single infer_not_in_range
// without re-encoding Equals. run_test_and_verify then has VeriPB check the whole
// proof. The hole on x is deliberately wide so the inference's width-independence is
// exercised on a non-trivial interval.
auto main() -> int
{
    Problem p;

    // x misses the wide block [10..30]; y misses [3..6]. Each side loses an interval to
    // the other: x drops [3..6] (absent from x already, so this side is small) and y
    // drops the wide [10..30] (absent from x).
    vector<Integer> xd, yd;
    for (int i = 0; i <= 40; ++i) {
        if (i < 10 || i > 30)
            xd.push_back(Integer{i});
        if (i < 3 || i > 6)
            yd.push_back(Integer{i});
    }
    auto x = p.create_integer_variable(xd, "x");
    auto y = p.create_integer_variable(yd, "y");

    p.post(Equals{x, y});

    solve(
        p, [](const CurrentState &) -> bool { return true; },
        ProofOptions{"range_infer_test"});

    return 0;
}
