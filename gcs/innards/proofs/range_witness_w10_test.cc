#include <gcs/constraints/plus.hh>
#include <gcs/current_state.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <vector>

using namespace gcs;
using std::vector;

// Witness W10 (see dev_docs/range_literals_spec.md): a range literal that the OPB
// defines has to be linked at proof start. Each holey domain below is posted as an
// In over its values, whose at-least-one row names one range literal per run of
// two or more of them ([a in 9..11], [a in 13..17] and so on), defined by the OPB
// rather than the proof. The OPB cannot also state the partition, coverings and
// containment edges that keep unit propagation strong enough over such a literal,
// so emit_delayed_proof_steps requests each one once the proof starts, which
// links it exactly as if the proof's first step had asked for it.
//
// Leave that request out and the literals are linked only when something in the
// proof first names them, while the at-least-one rows mention them from the start,
// and this run's proof is rejected at a backtrack clause. The branching is seeded
// random, which is what reaches that: no scripted order has been found that does.
// The seed was picked from a sweep in which 3 of 100 seeds bite and every seed
// verifies with the request in place. std::uniform_int_distribution is
// implementation-defined, so the order -- and so the bite -- is libstdc++'s; under
// another standard library this still verifies, but may not witness anything.
auto main() -> int
{
    Problem p;
    auto a = p.create_integer_variable(vector{7_i, 9_i, 10_i, 11_i, 13_i, 14_i, 15_i, 16_i, 17_i}, "a");
    auto b = p.create_integer_variable(vector{10_i, 11_i, 13_i, 14_i, 15_i, 16_i, 17_i}, "b");
    auto c = p.create_integer_variable(vector{15_i, 16_i, 17_i, 19_i, 21_i, 25_i, 26_i}, "c");
    p.post(Plus{a, b, c}.with_consistency(consistency::GAC{}));

    solve_with(p,      //
        SolveCallbacks{//
            .solution = [](const CurrentState &) -> bool { return true; },
            .branch = branch_with(variable_order::random(p, 15), value_order::reject_random_interval(16))},
        ProofOptions{"range_witness_w10_test"});

    return 0;
}
