#include <gcs/constraints/equals.hh>
#include <gcs/current_state.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <vector>

using namespace gcs;
using std::vector;

// Witness W6 (see dev_docs/range_literals_spec.md §8 and dev_docs/view-range-literals.md):
// an interval fact concluded on a plain variable has to reach a reason literal on a
// *view* of it. This is W2's shape with the reason moved across a view boundary.
//
// `b`'s initial domain {0, 4} makes In conclude one interval fact ~[b in 1..3], over
// `b` itself. `Equals(a, b + 10)` then prunes `a` with a reason naming the same run on
// the view, ~[view in 11..13]. Those are two different literals over two different bit
// vectors, and the replay of the first backtrack clause has to get from the first to
// the second by unit propagation.
//
// Everything about the numbers is load-bearing, because the crossing happens by
// accident in most configurations (measured: about 80% of small random ones):
//
//   - 11 > 10 and 13 < 14, so the run is strictly inside the view's definition bounds.
//     A run that touched either bound would cross for free: the boundary pin makes the
//     reverse reification a unit, and the far side's forward reification finishes it.
//   - `b`'s only interior cell is the whole of [1, 3], width 3 and never split, because
//     nothing in this problem ever mentions b = 1, 2 or 3. One eq atom anywhere inside
//     would shatter the cell on both sides and the crossing would again come for free.
//   - `a`'s domain is the view's, so the prune is one interval rather than three
//     disequalities, which is what puts an interval literal in the reason at all.
//
// Without the link clause pair emitted by need_invar, the replay stalls: ~[b in 1..3]
// descends b's own containment edges and finds nothing below to carry across.
namespace
{
    auto scripted_neq_then_eq(IntegerVariableID var, Integer val) -> BranchHeuristic
    {
        return [var, val](const Problem &, innards::State &, innards::Propagators &) -> BranchCallback {
            return [var, val](const CurrentState & state, const innards::Propagators &) -> std::generator<IntegerVariableCondition> {
                return [](const CurrentState & state, IntegerVariableID var, Integer val) -> std::generator<IntegerVariableCondition> {
                    if (state.domain_size(var) >= 2_i && state.in_domain(var, val)) {
                        co_yield var != val;
                        co_yield var == val;
                    }
                }(state, var, val);
            };
        };
    }
}

auto main() -> int
{
    Problem p;
    auto a = p.create_integer_variable(10_i, 14_i, "a");
    auto b = p.create_integer_variable(vector{0_i, 4_i}, "b");
    auto view = b + 10_i;

    p.post(Equals{a, view});
    p.post(NotEquals{a, view});

    solve_with(p,      //
        SolveCallbacks{//
            .solution = [](const CurrentState &) -> bool { return true; },
            .branch = branch_sequence(scripted_neq_then_eq(a, 10_i), branch_with(variable_order::dom_then_deg(p), value_order::smallest_first()))},
        ProofOptions{"range_witness_w6_test"});

    return 0;
}
