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

// A constant in the successor array, together with a reachability walk that actually
// fires. Both halves are needed to reach the pigeonhole in derive_unreachable, and no
// other fixture puts them together --- which is how issue #812 stayed hidden while every
// mario instance tripped over it, mario's `succ[LuigiHouse] = MarioHouse` folding into the
// array as a literal.
//
// Six nodes. Node 0 is the anchor, its own index left out of its domain, and succ[4] is
// the **constant** 0 --- not a singleton-domain variable, which goes through an entirely
// different path in the proof layer; it is the constant that is the bug. Following the
// edges from the anchor reaches {0,2,3,4} and never nodes 1 or 5, so both must opt out.
//
// Two details make this fixture able to tell the fix from the bug, and a smaller one could
// not:
//
//   * **the unreachable value has two candidate takers.** Nodes 1 and 5 can each point at
//     the other, so "somebody takes the value 1" genuinely needs the pigeonhole count.
//     With only one candidate, unit propagation reaches the conclusion unaided and a broken
//     count goes unnoticed --- an earlier five-node version of this test had exactly that
//     flaw and passed with the fix's key row deleted.
//   * **the pinned value 0 is in a variable's declared domain** (node 2's). Otherwise
//     at-most-one over the variables is already as strong as at-most-zero, and the row the
//     fix adds changes nothing in the arithmetic.
//
// Two solutions: 0 -> 2 -> 4 -> 0 and 0 -> 3 -> 4 -> 0, with the rest opting out. Node 4 is
// on the tour of both, its constant successor being 0.
auto build(Problem & p) -> vector<IntegerVariableID>
{
    vector<IntegerVariableID> succ;
    succ.push_back(p.create_integer_variable(vector<Integer>{2_i, 3_i}, "succ0"));
    succ.push_back(p.create_integer_variable(vector<Integer>{1_i, 5_i}, "succ1"));
    succ.push_back(p.create_integer_variable(vector<Integer>{0_i, 2_i, 4_i}, "succ2"));
    succ.push_back(p.create_integer_variable(vector<Integer>{3_i, 4_i}, "succ3"));
    succ.push_back(ConstantIntegerVariableID{0_i});
    succ.push_back(p.create_integer_variable(vector<Integer>{1_i, 5_i}, "succ5"));
    return succ;
}

// The scenario above pins that the certificate no longer *throws*, which is the bug in
// #812's title. It does not pin that the replacement counting is right: at n <= 6 unit
// propagation reaches E(t, x) from the candidate rows and the reason alone, so the
// pigeonhole line is not load-bearing there at all, and deleting the row the fix adds still
// verifies. The whole anchored enumeration sweep has the same weakness, and cannot be run
// at a size where it does not, complete enumeration being what it is.
//
// So this second scenario, found by generation: eight nodes, a constant successor, no
// solution, and a proof that *fails* if the pinned value is counted with an ordinary
// at-most-one instead of at-most-zero. It is asymmetric and arbitrary because it was
// searched for rather than designed --- what was searched for is exactly the property that
// the fix's arithmetic is the only thing that closes it.
auto build_counting(Problem & p) -> vector<IntegerVariableID>
{
    vector<IntegerVariableID> succ;
    succ.push_back(p.create_integer_variable(vector<Integer>{1_i, 5_i}, "succ0"));
    succ.push_back(p.create_integer_variable(vector<Integer>{1_i, 4_i}, "succ1"));
    succ.push_back(p.create_integer_variable(vector<Integer>{0_i, 1_i, 2_i, 5_i, 6_i, 7_i}, "succ2"));
    succ.push_back(p.create_integer_variable(vector<Integer>{1_i, 2_i, 6_i}, "succ3"));
    succ.push_back(ConstantIntegerVariableID{6_i});
    succ.push_back(p.create_integer_variable(vector<Integer>{0_i, 1_i, 4_i, 5_i, 6_i}, "succ5"));
    succ.push_back(p.create_integer_variable(vector<Integer>{0_i, 4_i, 5_i, 6_i, 7_i}, "succ6"));
    succ.push_back(p.create_integer_variable(vector<Integer>{0_i, 1_i, 2_i, 5_i, 6_i, 7_i}, "succ7"));
    return succ;
}

auto run(bool proofs) -> long
{
    Problem p;
    auto succ = build(p);
    p.post(SubCircuit{succ}.with_algorithm(subcircuit::SCC{}));

    auto proof_name = proofs ? make_optional<std::string>("subcircuit_constant_test") : nullopt;
    long found = 0;
    auto stats = solve_with(p, //
        SolveCallbacks{        //
            .solution = [&](const CurrentState &) -> bool {
                ++found;
                return true;
            }},
        proof_name ? make_optional<ProofOptions>(*proof_name) : nullopt);

    cout << "constant successor, proofs " << (proofs ? "on" : "off") << ": " << found << " solutions, " << stats.recursions << " recursions" << endl;

    if (proof_name && ! verify_proof_and_dispose(*proof_name))
        return -1;

    return found;
}

auto run_counting(bool proofs) -> long
{
    Problem p;
    auto succ = build_counting(p);
    p.post(SubCircuit{succ}.with_algorithm(subcircuit::SCC{}));

    auto proof_name = proofs ? make_optional<std::string>("subcircuit_constant_counting_test") : nullopt;
    long found = 0;
    auto stats = solve_with(p, //
        SolveCallbacks{        //
            .solution = [&](const CurrentState &) -> bool {
                ++found;
                return true;
            }},
        proof_name ? make_optional<ProofOptions>(*proof_name) : nullopt);

    cout << "counting scenario, proofs " << (proofs ? "on" : "off") << ": " << found << " solutions, " << stats.recursions << " recursions" << endl;

    if (proof_name && ! verify_proof_and_dispose(*proof_name))
        return -1;

    return found;
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    constexpr long expected = 2;

    auto without = run(false);
    if (without != expected) {
        cout << "expected " << expected << " solutions without proofs, got " << without << endl;
        return EXIT_FAILURE;
    }

    // The point of the test: the same answer, with a proof that verifies. Before #812 was
    // fixed this threw an UnimplementedException from the pigeonhole instead.
    auto with = run(can_run_veripb());
    if (with != expected) {
        cout << "expected " << expected << " solutions with proofs, got " << with << endl;
        return EXIT_FAILURE;
    }

    // And the scenario whose proof only closes if the replacement counting is right.
    if (run_counting(false) != 0) {
        cout << "expected the counting scenario to have no solutions" << endl;
        return EXIT_FAILURE;
    }
    if (run_counting(can_run_veripb()) != 0) {
        cout << "the counting scenario's proof did not verify" << endl;
        return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}
