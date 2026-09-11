#include <gcs/constraints/equals.hh>
#include <gcs/current_state.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <vector>

using namespace gcs;
using std::vector;

// Witness W9 (see dev_docs/range_literals_spec.md §8 and dev_docs/view-range-literals.md):
// W8's two-view form, and the one that shows the crossing has to compose. Two views of
// the same variable, `b + 10` and `b + 20`, each with their own encoded variable and
// their own partition; nothing joins the two views directly, so a fact travelling from
// one to the other goes through `b` and needs both links on the way.
//
// The shape:
//   - Equals(a, view1) at the root carves [1..2] and [6..7] out of `b`, which leaves
//     [3..5] on `b`, [13..15] on view1 and [23..25] on view2 as unnamed partition cells.
//   - the decision ~[a in 13..15] makes Equals(a, view1) *conclude* ~[view1 in 13..15],
//     which is one of those cells -- so here the unlinked literal is a conclusion
//     rather than a decision, the other way round from W8.
//   - Equals(a2, view2) then reasons with ~[view2 in 21..27], whose covering needs
//     ~[view2 in 23..25]. Getting there means view1 -> b -> view2.
//
// Together with W8 this pins down that linking has to happen when a literal is named,
// on either side and whichever role it plays.

namespace
{
    // Reject [lo, hi] on var, then accept it. Guarded so it only fires while var still
    // has values outside the interval, so the accept branch does not re-reject.
    auto scripted_reject_then_accept(IntegerVariableID var, Integer lo, Integer hi) -> BranchHeuristic
    {
        return [var, lo, hi](const Problem &, innards::State &, innards::Propagators &) -> BranchCallback {
            return [var, lo, hi](const CurrentState & state, const innards::Propagators &) -> std::generator<IntegerVariableCondition> {
                return [](const CurrentState & state, IntegerVariableID var, Integer lo, Integer hi) -> std::generator<IntegerVariableCondition> {
                    if (state.in_domain(var, lo) && state.in_domain(var, hi) && state.domain_size(var) > hi - lo + 1_i) {
                        co_yield not_in_range(var, lo, hi);
                        co_yield in_range(var, lo, hi);
                    }
                }(state, var, lo, hi);
            };
        };
    }

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
    auto a = p.create_integer_variable(vector{10_i, 13_i, 14_i, 15_i, 18_i}, "a");
    auto b = p.create_integer_variable(0_i, 8_i, "b");
    auto a2 = p.create_integer_variable(20_i, 28_i, "a2");
    auto view1 = b + 10_i;
    auto view2 = b + 20_i;

    p.post(Equals{a, view1});
    p.post(Equals{a2, view2});
    p.post(NotEquals{a2, view2});

    solve_with(p,      //
        SolveCallbacks{//
            .solution = [](const CurrentState &) -> bool { return true; },
            .branch = branch_sequence(scripted_reject_then_accept(a, 13_i, 15_i),
                branch_sequence(scripted_neq_then_eq(a2, 20_i), branch_with(variable_order::dom_then_deg(p), value_order::smallest_first())))},
        ProofOptions{"range_witness_w9_test"});

    return 0;
}
