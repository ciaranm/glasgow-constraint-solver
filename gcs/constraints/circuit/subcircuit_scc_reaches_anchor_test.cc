#include <gcs/constraints/circuit.hh>
#include <gcs/constraints/in.hh>
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
using std::pair;
using std::vector;

// The half of the reachability rule that reads the arrows backwards: a node on the tour has
// to reach the anchor, not merely be reachable from it.
//
// Twelve nodes again, and again the lower six point only within themselves, so none of them
// can reach the anchor in the upper half. What is different from subcircuit_scc_test is one
// extra arrow, from node 7 down to node 0: it makes every node in the problem reachable
// *from* the anchor, so the forward walk has nothing at all to say here, and the six
// opt-outs at the root can only come from reading the arrows the other way. Delete the
// backwards walk and this test goes red where subcircuit_scc_test stays green.
//
// The solution count is the same 325 as in that test, for the same reason: node 6 cannot
// point at itself, so the tour must run through the upper half, and the lower half's arrow
// budget gives it no way back. Node 7's extra arrow is dead on arrival -- once node 0 is a
// self loop, all-different takes value 0 off node 7 -- which is the point: it changes what
// the propagator can see without changing what the answer is.

auto post_constraints(Problem & p, vector<IntegerVariableID> & nodes) -> void
{
    // The lower half: node i points at itself or at the next one round, and nowhere else.
    // These are the smallest domains in the problem, so the brancher walks in here first.
    for (int i = 0; i < 6; ++i)
        p.post(In{nodes[static_cast<std::size_t>(i)], {Integer{i}, Integer{(i + 1) % 6}}});

    // The upper half points within itself, except that node 7 may also point at node 0,
    // which is what puts the lower half within the anchor's reach.
    for (int i = 6; i < 12; ++i) {
        vector<Integer> values;
        if (i == 7)
            values.emplace_back(0_i);
        for (int v = 6; v < 12; ++v)
            if (! (i == 6 && v == 6))
                values.emplace_back(Integer{v});
        p.post(In{nodes[static_cast<std::size_t>(i)], values});
    }
}

// The state at the first search node, which is the root after propagation, and the place
// where the two algorithms differ crisply.
auto run(SubCircuitAlgorithm algorithm, const ViewWrapConfig & view_cfg, const std::string & label, long & lower_half_fixed_at_root) -> long
{
    constexpr int n_positions = 12;
    auto wraps = wraps_for_positions(view_cfg, n_positions);

    Problem p;
    // As in subcircuit_scc_test: the anchor's own index has to be outside its *declared*
    // domain, since that is what with_required_node() checks, so node 6 starts at 7 -- and a
    // view keeps that domain, being the same variable seen through an offset, which is what
    // lets this scenario go through the view sweep.
    vector<IntegerVariableID> nodes;
    for (int i = 0; i < n_positions; ++i)
        nodes.push_back(
            create_integer_variable_or_constant_with_view(p, pair{i == 6 ? 7 : 0, n_positions - 1}, wraps.at(static_cast<std::size_t>(i))));

    post_constraints(p, nodes);
    p.post(SubCircuit{nodes}.with_required_node(6).with_algorithm(algorithm));

    bool proofs = can_run_veripb();
    auto proof_name = proofs ? make_optional("subcircuit_scc_reaches_anchor_test_" + label + "_" + view_wrap_config_label(view_cfg)) : nullopt;
    long found = 0;
    auto seen_root = false;
    lower_half_fixed_at_root = 0;
    auto stats = solve_with(p, //
        SolveCallbacks{        //
            .solution = [&](const CurrentState &) -> bool {
                ++found;
                return true;
            },
            .trace = [&](const CurrentState & s) -> bool {
                if (! seen_root) {
                    seen_root = true;
                    for (int i = 0; i < 6; ++i)
                        if (s.has_single_value(nodes[static_cast<std::size_t>(i)]) && s(nodes[static_cast<std::size_t>(i)]) == Integer{i})
                            ++lower_half_fixed_at_root;
                }
                return true;
            }},
        proof_name ? make_optional<ProofOptions>(*proof_name) : nullopt);

    cout << label << ": " << found << " solutions, " << stats.recursions << " recursions, " << lower_half_fixed_at_root
         << " of the stranded half opted out at the root" << endl;

    if (proof_name && ! verify_proof_and_dispose(*proof_name))
        return -1;

    return found;
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    constexpr int n_positions = 12;
    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        cout << "subcircuit_scc_reaches_anchor view sweep: position " << *view_cfg.single_position
             << " out of range for n_positions = " << n_positions << "; skipping" << endl;
        return EXIT_SUCCESS;
    }

    constexpr long expected_solutions = 325;

    long prevent_at_root = 0, scc_at_root = 0;
    auto with_prevent = run(subcircuit::Prevent{}, view_cfg, "prevent", prevent_at_root);
    auto with_scc = run(subcircuit::SCC{}, view_cfg, "scc", scc_at_root);

    if (with_prevent != expected_solutions || with_scc != expected_solutions) {
        cout << "expected " << expected_solutions << " solutions from each" << endl;
        return EXIT_FAILURE;
    }

    if (scc_at_root != 6) {
        cout << "expected the whole stranded half to opt out at the root, got " << scc_at_root << " of 6" << endl;
        return EXIT_FAILURE;
    }

    if (prevent_at_root != 0) {
        cout << "expected check-and-prevent to opt none of it out at the root, got " << prevent_at_root << endl;
        return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}
