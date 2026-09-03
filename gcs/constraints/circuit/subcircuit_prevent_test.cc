#include <gcs/constraints/circuit.hh>
#include <gcs/constraints/in.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::test_innards;

using std::cout;
using std::endl;
using std::make_optional;
using std::nullopt;
using std::vector;

// The evidence-node inference, driven directly and with the anchor left undetermined:
// nodes 0, 1 and 2 stay wide open, so which node is the tour's first is not yet decided
// when the chain 3 -> 4 -> 5 is stopped from closing.
//
// This began life as the test that showed derive_tour_at_most() was load-bearing, because
// the enumeration in subcircuit_test.cc could not: with off-tour positions numbered after
// the on-tour ones, unit propagation found the conflict unaided at every n that test runs.
// Pinning off-tour positions to zero changed that, and the enumeration now catches a
// missing certificate at n = 5 on its own, so this is no longer the mutation test -- it is
// a targeted regression test for the evidence-node path and the undetermined anchor, which
// is worth keeping for its own sake but no longer carries that argument.

auto post_constraints(Problem & p, vector<IntegerVariableID> & nodes) -> void
{
    // The forced chain is 3 -> 4 -> 5, and its only closing value is succ[5] = 3.
    p.post(In{nodes[3], {4_i}});
    p.post(In{nodes[4], {5_i}});
    p.post(In{nodes[5], {3_i, 6_i}});
    // Node 7 cannot be a self loop, so it must be on the tour: it is the evidence node,
    // and it is outside the chain, so closing the chain would leave it nowhere to go.
    p.post(In{nodes[7], {0_i, 1_i, 2_i, 3_i, 4_i, 5_i, 6_i}});
    // Nodes 0, 1 and 2 stay wide open, which is the point: whether each of them is on the
    // tour is still unknown, so unit propagation cannot tell which node is the tour's
    // first, and the certificate has to cover every candidate.
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    constexpr int n_positions = 8;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        cout << "subcircuit_prevent view sweep: position " << *view_cfg.single_position << " out of range for n_positions = " << n_positions
             << "; skipping" << endl;
        return EXIT_SUCCESS;
    }
    auto wraps = wraps_for_positions(view_cfg, n_positions);

    Problem p;
    vector<IntegerVariableID> nodes;
    for (int i = 0; i < n_positions; ++i)
        nodes.push_back(create_integer_variable_or_constant_with_view(p, std::pair{0, n_positions - 1}, wraps.at(i)));

    post_constraints(p, nodes);
    p.post(SubCircuit{nodes}.with_algorithm(subcircuit::Prevent{}));

    bool proofs = can_run_veripb();
    auto proof_name = proofs ? make_optional("subcircuit_prevent_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    auto stats = solve_with(p, //
        SolveCallbacks{        //
            .solution = [&](const CurrentState & s) -> bool {
                for (const auto & v : nodes)
                    cout << s(v) << " ";
                cout << endl;
                return true;
            }},
        proof_name ? make_optional<ProofOptions>(*proof_name) : nullopt);

    cout << stats;

    if (proof_name)
        if (! verify_proof_and_dispose(*proof_name))
            return EXIT_FAILURE;

    return EXIT_SUCCESS;
}
