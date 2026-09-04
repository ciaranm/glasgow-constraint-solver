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

// Francis and Stuckey's prune within, isolated: the same shave prune root does, over a node
// that is not the anchor.
//
// Unlike the prune root scenario, this instance was *found* rather than built. Hand-building
// one kept producing structures that were unsatisfiable instead: the rule wants a component
// whose only way back to the anchor is through the node being shaved, and saying that in a
// domain tends to say at the same time that no tour exists at all. So a generator drew
// random domains over seven nodes and kept the first one where prune within shrinks a root
// domain, the plain walks and prune root do not, and there is a real solution set --- which
// is also why nothing here is symmetric or tidy.
//
// Nodes 0 and 1 have their own indices left out, so both must be on the tour and node 0 is
// the anchor. What prune within finds is that two of the seven values node 2's successor
// could take would strand something: it goes from seven values to five at the root, and
// neither the plain walk nor prune root touches it.
//
// Both certificate directions fire here, which the prune root scenario did not exercise:
// ten of the prunings come from the forward walk and six from the backward one.
auto build(Problem & p, IntegerVariableID & witness) -> vector<IntegerVariableID>
{
    // As in the prune root test, the witness only exists so that the root is a search node
    // rather than a solution, since that is where the trace callback reads the root state.
    witness = p.create_integer_variable(0_i, 1_i, "witness");

    vector<IntegerVariableID> succ;
    succ.push_back(p.create_integer_variable(vector<Integer>{2_i, 3_i, 6_i}, "succ0"));
    succ.push_back(p.create_integer_variable(vector<Integer>{2_i, 4_i}, "succ1"));
    succ.push_back(p.create_integer_variable(vector<Integer>{0_i, 1_i, 2_i, 3_i, 4_i, 5_i, 6_i}, "succ2"));
    succ.push_back(p.create_integer_variable(vector<Integer>{0_i, 4_i, 5_i}, "succ3"));
    succ.push_back(p.create_integer_variable(vector<Integer>{2_i, 4_i}, "succ4"));
    succ.push_back(p.create_integer_variable(vector<Integer>{0_i, 1_i, 3_i, 6_i}, "succ5"));
    succ.push_back(p.create_integer_variable(vector<Integer>{0_i, 1_i, 3_i, 4_i}, "succ6"));
    return succ;
}

// The node whose successor prune within shaves, and how many values it has at the root.
constexpr std::size_t shaved_node = 2;

auto run(bool prune_root, bool prune_within, const std::string & label, long & values_at_root) -> long
{
    Problem p;
    IntegerVariableID witness{ConstantIntegerVariableID{0_i}};
    auto succ = build(p, witness);
    auto constraint = SubCircuit{succ}.with_algorithm(subcircuit::SCC{});
    if (prune_root)
        constraint.with_prune_root();
    if (prune_within)
        constraint.with_prune_within();
    p.post(std::move(constraint));

    auto proofs = can_run_veripb();
    auto proof_name = proofs ? make_optional("subcircuit_prune_within_test_" + label) : nullopt;

    long found = 0;
    auto seen_root = false;
    values_at_root = 0;
    auto stats = solve_with(p, //
        SolveCallbacks{        //
            .solution = [&](const CurrentState &) -> bool {
                ++found;
                return true;
            },
            .trace = [&](const CurrentState & s) -> bool {
                if (! seen_root) {
                    seen_root = true;
                    values_at_root = s.domain_size(succ[shaved_node]).raw_value;
                }
                return true;
            }},
        proof_name ? make_optional<ProofOptions>(*proof_name) : nullopt);

    cout << label << ": " << found << " solutions, " << stats.recursions << " recursions, succ[" << shaved_node << "] had " << values_at_root
         << " values at the root" << endl;

    if (proof_name && ! verify_proof_and_dispose(*proof_name))
        return -1;

    return found;
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    long plain_at_root = 0, root_at_root = 0, within_at_root = 0;
    auto plain = run(false, false, "scc", plain_at_root);
    auto with_root = run(true, false, "scc_prune_root", root_at_root);
    auto with_within = run(false, true, "scc_prune_within", within_at_root);

    // The rules strengthen an inference, not the constraint, so all three enumerate the
    // same set. Twenty, being the ten subcircuits times the witness's two values.
    constexpr long expected = 20;
    if (plain != expected || with_root != expected || with_within != expected) {
        cout << "expected " << expected << " solutions from each, got " << plain << ", " << with_root << " and " << with_within << endl;
        return EXIT_FAILURE;
    }

    if (plain_at_root != 7) {
        cout << "expected the plain walk to leave succ[" << shaved_node << "] all seven values at the root, got " << plain_at_root << endl;
        return EXIT_FAILURE;
    }

    // Prune root is over the anchor's successor only, and this is not the anchor, so it must
    // leave this domain exactly as the plain walk did. That is what makes this test about
    // prune within rather than about the shave in general.
    if (root_at_root != plain_at_root) {
        cout << "expected prune root to leave succ[" << shaved_node << "] alone, got " << root_at_root << " against " << plain_at_root << endl;
        return EXIT_FAILURE;
    }

    if (within_at_root != 5) {
        cout << "expected prune within to take succ[" << shaved_node << "] to five values at the root, got " << within_at_root << endl;
        return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}
