#include <gcs/constraints/circuit.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <string>
#include <vector>

using namespace gcs;
using namespace gcs::test_innards;

using std::cout;
using std::endl;
using std::make_optional;
using std::nullopt;
using std::vector;

// Francis and Stuckey's prune root, isolated. The scenario has to make the rule the *only*
// route to its own conclusion, which rules out most of the obvious constructions:
//
//   * the plain forward walk must not get there, and that part is automatic. With the
//     anchor's successor still free the anchor reaches everything any of its candidates
//     reaches, so there is nothing unreachable to report --- which is exactly why the rule
//     exists, and why it costs a walk per candidate.
//   * the plain *backward* walk must not get there either, and that is the part needing
//     care. An earlier version of this scenario gave a component just one edge back to the
//     anchor, and all-different went on to remove that value; the backward walk then
//     stranded the whole component by itself and reached the same conclusion for free. So
//     every component here has two edges back to the anchor.
//   * `check` and `prevent` must not get there, which means nothing may become fixed: one
//     fixed successor cascades through all-different, a cycle closes, and a closed cycle
//     forces everyone outside it off the tour. So no domain here is a singleton.
//
// Seven nodes. The anchor is node 0, its own index left out of its domain, so it is
// declared on the tour; its two candidate values are the two components it could enter.
// Neither component has an edge to the other, and both have two edges back to node 0.
// Node 4's own index is left out too, so node 4 must be on the tour as well --- and its
// component is reachable only through the edge 0 -> 4.
//
// So assuming 0 -> 1 leaves node 4 unreachable, and the value 1 has to go. Nothing else in
// the model can tell the two candidates apart, which is what the root-state check below
// pins down.
//
// The four subcircuits are 0 -> 4 -> 5 -> 0, 0 -> 4 -> 6 -> 0, 0 -> 4 -> 5 -> 6 -> 0 and
// 0 -> 4 -> 6 -> 5 -> 0, with 1, 2 and 3 opting out of each.

// The witness is not part of the scenario: it exists so that the root is a search node
// rather than a solution, since the trace callback --- which is where the root state is
// read --- fires only at nodes that are not already solutions. Two values, so the eight
// solutions are the four subcircuits twice.
auto build(Problem & p, IntegerVariableID & witness) -> vector<IntegerVariableID>
{
    witness = p.create_integer_variable(0_i, 1_i, "witness");

    vector<IntegerVariableID> succ;
    // Node 0: the anchor. 0 is not in its own domain, which is what declares it on the tour.
    succ.push_back(p.create_integer_variable(vector<Integer>{1_i, 4_i}, "succ0"));
    // {1,2,3}: no edge to the other component, and two edges back to the anchor (2 -> 0 and
    // 3 -> 0) so that losing one does not strand the component.
    succ.push_back(p.create_integer_variable(vector<Integer>{1_i, 2_i, 3_i}, "succ1"));
    succ.push_back(p.create_integer_variable(vector<Integer>{0_i, 1_i, 2_i, 3_i}, "succ2"));
    succ.push_back(p.create_integer_variable(vector<Integer>{0_i, 1_i, 2_i, 3_i}, "succ3"));
    // {4,5,6}: likewise, and node 4 must be on the tour, its own index being left out. The
    // component is reachable from the anchor only through 0 -> 4.
    succ.push_back(p.create_integer_variable(vector<Integer>{5_i, 6_i}, "succ4"));
    succ.push_back(p.create_integer_variable(vector<Integer>{0_i, 4_i, 5_i, 6_i}, "succ5"));
    succ.push_back(p.create_integer_variable(vector<Integer>{0_i, 4_i, 5_i, 6_i}, "succ6"));
    return succ;
}

// Returns the number of solutions, and reports through `anchor_values_at_root` how many
// values the anchor's successor still had after the root propagation. That is where the two
// configurations differ crisply, and asserting on it rather than on a recursion count is
// what stops a rule that infers nothing from passing.
auto run(bool prune_root, const std::string & label, long & anchor_values_at_root) -> long
{
    Problem p;
    IntegerVariableID witness{ConstantIntegerVariableID{0_i}};
    auto succ = build(p, witness);
    auto constraint = SubCircuit{succ}.with_algorithm(subcircuit::SCC{});
    if (prune_root)
        constraint.with_prune_root();
    p.post(std::move(constraint));

    auto proofs = can_run_veripb();
    auto proof_name = proofs ? make_optional("subcircuit_prune_root_test_" + label) : nullopt;

    long found = 0;
    auto seen_root = false;
    anchor_values_at_root = 0;
    auto stats = solve_with(p, //
        SolveCallbacks{        //
            .solution = [&](const CurrentState &) -> bool {
                ++found;
                return true;
            },
            .trace = [&](const CurrentState & s) -> bool {
                if (! seen_root) {
                    seen_root = true;
                    anchor_values_at_root = s.domain_size(succ[0]).raw_value;
                }
                return true;
            }},
        proof_name ? make_optional<ProofOptions>(*proof_name) : nullopt);

    cout << label << ": " << found << " solutions, " << stats.recursions << " recursions, anchor successor had " << anchor_values_at_root
         << " values at the root" << endl;

    if (proof_name && ! verify_proof_and_dispose(*proof_name))
        return -1;

    return found;
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    long plain_at_root = 0, pruned_at_root = 0;
    auto plain = run(false, "scc", plain_at_root);
    auto pruned = run(true, "scc_prune_root", pruned_at_root);

    // Same solution set: the rule strengthens an inference, not the constraint. Eight,
    // being the four subcircuits times the witness's two values.
    if (plain != 8 || pruned != 8) {
        cout << "expected eight solutions from each, got " << plain << " and " << pruned << endl;
        return EXIT_FAILURE;
    }

    // And it did something. Without the rule the anchor keeps both candidates at the root,
    // because nothing else in the model can tell them apart; with it, the one that strands
    // node 4 is gone and the successor is fixed.
    if (plain_at_root != 2) {
        cout << "expected the plain walk to leave the anchor both candidates at the root, got " << plain_at_root << endl;
        return EXIT_FAILURE;
    }

    if (pruned_at_root != 1) {
        cout << "expected prune root to fix the anchor's successor at the root, got " << pruned_at_root << " values" << endl;
        return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}
