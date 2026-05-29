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

auto post_constraints(Problem & p, vector<IntegerVariableID> & nodes)
{
    p.post(In{nodes[0], {1_i, 4_i, 5_i}});
    p.post(In{nodes[1], {0_i, 2_i, 3_i}});
    p.post(In{nodes[2], {0_i, 1_i}});
    p.post(In{nodes[3], {1_i, 2_i}});
    p.post(In{nodes[4], {3_i, 0_i}});
    p.post(In{nodes[5], {4_i, 0_i}});
}
auto main(int argc, char * argv[]) -> int
{
    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    constexpr int n_positions = 6;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        cout << "circuit_prune_root view sweep: position " << *view_cfg.single_position
             << " out of range for n_positions = " << n_positions << "; skipping" << endl;
        return EXIT_SUCCESS;
    }
    auto wraps = wraps_for_positions(view_cfg, n_positions);

    Problem p;
    vector<IntegerVariableID> nodes;
    for (int i = 0; i < n_positions; ++i)
        nodes.push_back(create_integer_variable_or_constant_with_view(p, std::pair{0, n_positions - 1}, wraps.at(i)));

    post_constraints(p, nodes);

    p.post(CircuitSCC{nodes});

    bool proofs = can_run_veripb();
    auto proof_name = proofs ? make_optional("circuit_prune_root_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    auto stats = solve_with(
        p,
        SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
            for (const auto & v : nodes) {
                cout << s(v) << " ";
            }
            cout << endl;
            cout << 0 << " -> " << s(nodes[0]);
            auto current = s(nodes[0]);
            while (current != 0_i) {
                cout << " -> ";
                cout << s(nodes[current.as_index()]);
                current = s(nodes[current.as_index()]);
            }
            cout << "\n\n";
            return true;
        }},
        proof_name ? make_optional<ProofOptions>(*proof_name) : nullopt);

    cout << stats;

    if (proof_name)
        if (! run_veripb(*proof_name + ".opb", *proof_name + ".pbp"))
            return EXIT_FAILURE;

    return EXIT_SUCCESS;
}
