#include <gcs/constraints/equals.hh>
#include <gcs/current_state.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <vector>

using namespace gcs;
using std::vector;

// Witness W7 (see dev_docs/range_literals_spec.md §8 and dev_docs/view-range-literals.md):
// W6's mirror image. An interval fact concluded on a *view* has to reach a reason
// literal on the variable the view wraps.
//
// `Equals(b + 10, a)` with `a` in {10, 14} prunes the view, so the conclusion is
// logged as ~[view in 11..13] over the view's own bit vector. `Equals(b, c)` then
// prunes `c` with a reason naming the same run on `b`, ~[b in 1..3]. As in W6 those
// are two literals over two bit vectors and the replay has to cross between them by
// unit propagation, in the opposite direction.
//
// The same three things are load-bearing here, for the same reason (the crossing
// happens by accident in about 80% of small random configurations): [11, 13] is
// strictly inside the view's bounds 10..14 and [1, 3] strictly inside b's 0..4, so
// neither side gets the free crossing a boundary pin gives; and nothing in the problem
// mentions any of b = 1, 2, 3, so [1, 3] stays one unsplit width-3 cell on both sides.
// The NotEquals is only there to make the scripted decision fail and so force a
// backtrack clause whose replay has to re-derive the reason.
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
    auto a = p.create_integer_variable(vector{10_i, 14_i}, "a");
    auto b = p.create_integer_variable(0_i, 4_i, "b");
    auto c = p.create_integer_variable(0_i, 4_i, "c");

    p.post(Equals{b + 10_i, a});
    p.post(Equals{b, c});
    p.post(NotEquals{b, c});

    solve_with(p,      //
        SolveCallbacks{//
            .solution = [](const CurrentState &) -> bool { return true; },
            .branch = branch_sequence(scripted_neq_then_eq(c, 0_i), branch_with(variable_order::dom_then_deg(p), value_order::smallest_first()))},
        ProofOptions{"range_witness_w7_test"});

    return 0;
}
