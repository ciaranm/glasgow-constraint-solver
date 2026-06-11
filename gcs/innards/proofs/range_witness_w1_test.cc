#include <gcs/constraints/equals.hh>
#include <gcs/current_state.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <vector>

using namespace gcs;
using std::vector;

// Witness W1 (dev_docs/range_literals_spec.md §8): width-1 unification. Equals(a,b)
// removes the single value 1 from b; that removal and its reason must live on the eq
// atom `b = 1`, never on a width-1 range flag. A width-1 flag is an unlinked
// doppelganger of the eq atom (same boundary cuts, different Boolean, nothing
// connecting them), and the first backtrack clause's replay then stalls in six
// steps: "b lost 1" is locked inside ~f[in_b_1_1] with no link to b=1. The trace
// of that stall looks exactly like "unit propagation cannot thread a bound across
// the equality", which is the historical misdiagnosis this witness guards against.
namespace
{
    // Scripted first decision: where `var` is undecided and still has value 0,
    // branch var != 0 then var == 0 (only the root qualifies here); elsewhere fall
    // through to the default heuristic via branch_sequence.
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
    auto a = p.create_integer_variable(vector{0_i, 2_i, 3_i}, "a");
    auto b = p.create_integer_variable(vector{0_i, 1_i, 3_i}, "b");
    auto c = p.create_integer_variable(0_i, 3_i, "c");

    p.post(Equals{a, b});
    p.post(Equals{b, c});
    p.post(NotEquals{a, c});

    solve_with(
        p,
        SolveCallbacks{
            .solution = [](const CurrentState &) -> bool { return true; },
            .branch = branch_sequence(scripted_neq_then_eq_zero(c),
                branch_with(variable_order::dom_then_deg(p), value_order::smallest_first()))},
        ProofOptions{"range_witness_w1_test"});

    return 0;
}
