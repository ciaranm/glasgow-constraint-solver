#include <gcs/constraints/equals.hh>
#include <gcs/current_state.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>

#include <vector>

using namespace gcs;
using std::vector;

// Witness W2 (see dev_docs/range_literals_spec.md): reason falsifiability, exact
// match. The In constraint concludes b's initial-domain hole as one interval fact
// ~[b in 1..3]; Equals(a,b) then prunes a with a reason naming exactly that
// literal. If the reason's literal cannot be made true by unit propagation (no
// covering, or the hole concluded in a different vocabulary), the first backtrack
// clause's replay stalls in five steps. Two variables suffice, which also kills
// the "two-variable isolation is safe" testing heuristic: safety claims made on
// one vocabulary mode do not transfer.
namespace
{
    auto scripted_neq_then_eq_zero(IntegerVariableID var) -> BranchCallback
    {
        return [var](const CurrentState & state, const innards::Propagators &) -> std::generator<IntegerVariableCondition> {
            return [](const CurrentState & state, IntegerVariableID var) -> std::generator<IntegerVariableCondition> {
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
    auto a = p.create_integer_variable(0_i, 4_i, "a");
    auto b = p.create_integer_variable(vector{0_i, 4_i}, "b");

    p.post(Equals{a, b});
    p.post(NotEquals{a, b});

    solve_with(p,
        SolveCallbacks{.solution = [](const CurrentState &) -> bool { return true; },
            .branch = branch_sequence(scripted_neq_then_eq_zero(a), branch_with(variable_order::dom_then_deg(p), value_order::smallest_first()))},
        ProofOptions{"range_witness_w2_test"});

    return 0;
}
