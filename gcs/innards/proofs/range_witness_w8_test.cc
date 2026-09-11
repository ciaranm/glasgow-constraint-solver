#include <gcs/constraints/equals.hh>
#include <gcs/current_state.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <vector>

using namespace gcs;
using std::vector;

// Witness W8 (see dev_docs/range_literals_spec.md §8 and dev_docs/view-range-literals.md):
// a range literal that a *partition cell* already brought into existence still has to
// be linked across a view boundary when something later names it.
//
// W6 and W7 cover the crossing itself; this covers the trigger. A cell is created by
// ensure_partition_cut / init_interval_partition, straight through define_plain_invar,
// so it is never "requested" and `need_proof_name` short-circuits on it. Linking only
// what is requested therefore leaves exactly these literals unlinked, and they are
// invisible to any test whose decisions and reasons happen to name fresh intervals.
//
// The shape:
//   - `a`'s enumerated domain makes Equals(a, view) conclude ~[view in 11..12] and
//     ~[view in 16..17] at the root. Mirrored onto `b`, those two requests leave
//     [3..5] on `b` and [13..15] on the view as a partition cell nothing has named.
//   - the first decision is ~[b in 3..5]: an interval that already exists, as that
//     cell. Equals then prunes with a reason naming ~[view in 13..15].
//   - the remaining decisions drive the subtree to a conflict, so the backtrack
//     clause's replay has to carry the first fact to the second.
//
// Choosing 3..4 instead of 3..5 for the decision makes the same problem verify
// whether or not the link exists, because a fresh request is linked on the spot --
// which is the whole point: the discriminating instance is the one that names a cell.
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
    auto view = b + 10_i;

    p.post(Equals{a, view});
    p.post(NotEquals{a, view});

    solve_with(p,      //
        SolveCallbacks{//
            .solution = [](const CurrentState &) -> bool { return true; },
            .branch = branch_sequence(scripted_reject_then_accept(b, 3_i, 5_i),
                branch_sequence(scripted_neq_then_eq(a, 10_i),
                    branch_sequence(scripted_neq_then_eq(a, 15_i), branch_with(variable_order::dom_then_deg(p), value_order::smallest_first()))))},
        ProofOptions{"range_witness_w8_test"});

    return 0;
}
