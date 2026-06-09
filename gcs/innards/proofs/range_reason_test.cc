#include <gcs/constraints/element.hh>
#include <gcs/current_state.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <vector>

using namespace gcs;
using std::vector;

// Stage-2 integration check for range literals in reasons. A real solve whose
// generic_reason sees a contiguous domain hole of length >= 3, which forces the
// hole-coalescing path in ProofLogger::reason_to_lits to mint a single range
// literal ~[lo,hi] in place of per-value `idx != v` facts. Coalescing is enabled
// unconditionally here (so the test always exercises it, independent of how it is
// run); the run_test_and_verify harness then has VeriPB check the whole proof, so
// a broken coalesced reason would fail verification.
auto main() -> int
{
    ::setenv("GCS_RANGE_REASONS", "1", 1);

    Problem p;

    // Index variable with a built-in contiguous hole [3..8] (six missing values).
    auto idx = p.create_integer_variable(vector<Integer>{0_i, 1_i, 2_i, 9_i, 10_i, 11_i, 12_i}, "idx");
    auto res = p.create_integer_variable(0_i, 12_i, "res");

    // res = array[idx] with a distinct constant per index. The array entries at the
    // holed indices 3..8 have no support, so res loses those values -- each removal
    // justified by a reason over idx's holed domain, the coalescing target. GAC
    // (bounds_only = false) is needed to take the per-value-removal path.
    vector<Integer> array;
    for (int i = 0; i <= 12; ++i)
        array.push_back(Integer{i});

    p.post(ElementConstantArray{res, idx, array, false});

    solve(
        p, [](const CurrentState &) -> bool { return true; },
        ProofOptions{"range_reason_test"});

    return 0;
}
