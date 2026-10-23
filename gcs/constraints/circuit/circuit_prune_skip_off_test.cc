#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include <gcs/constraints/circuit.hh>
#include <gcs/constraints/in.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <util/enumerate.hh>

using namespace gcs;
using namespace gcs::test_innards;

using std::cmp_less;
using std::cout;
using std::endl;
using std::make_optional;
using std::nullopt;
using std::string;
using std::to_string;
using std::vector;

// Issue #1306: with prune skip off, an edge that skips a subtree stays in the
// graph, so the fix-required and no-back-edges certificates walked it and their
// reachable sets were no longer too small.

namespace
{
    struct Instance
    {
        string name;
        vector<vector<int>> domains;
        long expected_solutions;
    };

    const vector<Instance> instances = {
        // From the issue: every knob combination below wrote a proof that VeriPB
        // rejected, inside a fix-required or a no-back-edges certificate.
        {"issue",
            {
                {1, 3, 4},       //
                {0, 1, 2, 5},    //
                {0, 2, 3, 4, 5}, //
                {0, 2, 4},       //
                {2, 5},          //
                {0, 1, 2}        //
            },
            5},
        // The search from the root makes {1, 2} the first subtree and {3, 4} the
        // second, whose only back edge is (4, 2). Node 4's other edge goes to the
        // root, so it is proved absent rather than pruned, and fix required on
        // (4, 2) walks from 4 with no edge left at all: with prune skip on, 4 would
        // already be fixed and the rule would not fire.
        {"empty walk",
            {
                {1, 3}, //
                {0, 2}, //
                {0, 1}, //
                {0, 4}, //
                {0, 2}  //
            },
            1}};

    auto post_constraints(Problem & p, vector<IntegerVariableID> & nodes, const vector<vector<int>> & domains)
    {
        for (int i = 0; cmp_less(i, domains.size()); i++) {
            vector<Integer> int_domain{};
            for (const auto & val : domains[i]) {
                int_domain.emplace_back(val);
            }
            p.post((In{nodes[i], int_domain}));
        }
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);

    auto view_cfg = parse_view_wrap_config_from_argv(argc, argv);

    constexpr int n_positions = 6;
    if (view_cfg.single_position && (*view_cfg.single_position < 0 || *view_cfg.single_position >= n_positions)) {
        cout << "circuit_prune_skip_off view sweep: position " << *view_cfg.single_position << " out of range for n_positions = " << n_positions
             << "; skipping" << endl;
        return EXIT_SUCCESS;
    }
    auto wraps = wraps_for_positions(view_cfg, n_positions);

    bool proofs = can_run_veripb();

    for (const auto & [instance_index, instance] : enumerate(instances)) {
        for (bool fix_req : {true, false}) {
            for (bool prune_root : {true, false}) {
                int n = static_cast<int>(instance.domains.size());
                Problem p;
                vector<IntegerVariableID> nodes;
                for (int i = 0; i < n; ++i)
                    nodes.push_back(create_integer_variable_or_constant_with_view(p, std::pair{0, n - 1}, wraps.at(i)));

                post_constraints(p, nodes, instance.domains);

                p.post(Circuit{nodes}
                        .with_algorithm(circuit::SCC{})
                        .with_fix_req(fix_req)
                        .with_prune_root(prune_root)
                        .with_prune_within(false)
                        .with_prune_skip(false));

                auto label = instance.name + " fix_req=" + to_string(fix_req) + " prune_root=" + to_string(prune_root);
                auto proof_name = proofs ? make_optional("circuit_prune_skip_off_test_" + to_string(instance_index) + to_string(fix_req) +
                                               to_string(prune_root) + "_" + view_wrap_config_label(view_cfg))
                                         : nullopt;

                long solutions = 0;
                auto stats = solve_with(p, SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                    ++solutions;
                    return true;
                }},
                    proof_name ? make_optional<ProofOptions>(*proof_name) : nullopt);

                cout << label << ": " << solutions << " solutions\n" << stats;

                if (solutions != instance.expected_solutions) {
                    cout << label << ": expected " << instance.expected_solutions << " solutions" << endl;
                    return EXIT_FAILURE;
                }

                if (proof_name)
                    if (! verify_proof_and_dispose(*proof_name))
                        return EXIT_FAILURE;
            }
        }
    }

    return EXIT_SUCCESS;
}
