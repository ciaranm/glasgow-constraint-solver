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

auto main(int argc, char * argv[]) -> int
{
    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    constexpr int n_positions = 8;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        cout << "circuit_disconnected view sweep: position " << *view_cfg.single_position << " out of range for n_positions = " << n_positions
             << "; skipping" << endl;
        return EXIT_SUCCESS;
    }
    auto wraps = wraps_for_positions(view_cfg, n_positions);

    Problem p;

    std::vector<IntegerVariableID> x;
    for (int i = 0; i < n_positions; ++i)
        x.push_back(create_integer_variable_or_constant_with_view(p, std::pair{0, n_positions - 1}, wraps.at(i)));

    p.post(In{x[0], {1_i, 2_i, 3_i}});
    p.post(In{x[1], {3_i, 2_i}});
    p.post(In{x[2], {1_i, 3_i}});
    p.post(In{x[3], {2_i, 1_i}});

    p.post(In{x[4], {5_i, 6_i}});
    p.post(In{x[5], {7_i, 4_i}});
    p.post(In{x[6], {5_i, 7_i}});
    p.post(In{x[7], {4_i, 6_i}});

    p.post(Circuit{x}.with_algorithm(circuit::SCC{}));

    bool proofs = can_run_veripb();
    auto proof_name = proofs ? make_optional("circuit_disconnected_test_" + view_wrap_config_label(view_cfg)) : nullopt;
    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState &) -> bool {
                cout << "Solution:" << endl;
                return true;
            },
        },
        proof_name ? make_optional<ProofOptions>(*proof_name) : nullopt);

    cout << stats;

    if (proof_name)
        if (! run_veripb(*proof_name + ".opb", *proof_name + ".pbp"))
            return EXIT_FAILURE;

    return EXIT_SUCCESS;
}
