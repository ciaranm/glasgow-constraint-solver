#include <gcs/constraints/equals.hh>
#include <gcs/current_state.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <vector>

using namespace gcs;
using std::vector;

// Witness W3 (dev_docs/range_literals_spec.md §8): union coverage. b's combined
// hole [1,6] is concluded as two separate interval facts (~[b in 1..3] at root from
// In, ~[b in 4..6] from Equals(a,b)), but Equals(b,c)'s pruning reason names the
// union literal ~[b in 1..6]. Containment edges point the wrong way for this; only
// the covering emitted when [1,6] is minted as a union of adjacent cells lets the
// backtrack replay falsify it by unit propagation. This is the partition invariant
// (spec §3) earning its keep.
namespace
{
    auto scripted_neq_then_eq_zero(IntegerVariableID var) -> BranchCallback
    {
        return [var](const CurrentState & state, const innards::Propagators &) -> std::generator<BranchGuess> {
            return [](const CurrentState & state, IntegerVariableID var) -> std::generator<BranchGuess> {
                if (state.domain_size(var) >= 2_i && state.in_domain(var, 0_i)) {
                    co_yield var != 0_i;
                    co_yield var == 0_i;
                }
            }(state, var);
        };
    }
}

auto main() -> int
{
    Problem p;
    auto a = p.create_integer_variable(vector{0_i, 1_i, 2_i, 3_i, 7_i}, "a");
    auto b = p.create_integer_variable(vector{0_i, 4_i, 5_i, 6_i, 7_i}, "b");
    auto c = p.create_integer_variable(0_i, 7_i, "c");

    p.post(Equals{a, b});
    p.post(Equals{b, c});
    p.post(NotEquals{a, c});

    solve_with(
        p,
        SolveCallbacks{
            .solution = [](const CurrentState &) -> bool { return true; },
            .branch = branch_sequence(scripted_neq_then_eq_zero(c),
                branch_with(variable_order::dom_then_deg(p), value_order::smallest_first()))},
        ProofOptions{"range_witness_w3_test"});

    return 0;
}
