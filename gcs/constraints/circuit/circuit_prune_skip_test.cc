#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <iostream>

#include <gcs/constraints/circuit.hh>
#include <gcs/constraints/in.hh>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::make_optional;
using std::nullopt;
using std::string;
using std::vector;

auto post_constraints(Problem & p, vector<IntegerVariableID> & nodes)
{
    p.post(In{nodes[0], {1_i, 4_i, 5_i, 6_i}});
    p.post(In{nodes[1], {0_i, 2_i, 3_i}});
    p.post(In{nodes[2], {1_i, 3_i}});
    p.post(In{nodes[3], {1_i, 2_i}});
    p.post(In{nodes[4], {0_i, 1_i}});
    p.post(In{nodes[5], {0_i, 4_i, 6_i}});
    p.post(In{nodes[6], {0_i, 3_i, 5_i}});
}

auto main(int, char *[]) -> int
{
    Problem p;
    auto nodes = p.create_integer_variable_vector(7, 0_i, 6_i);

    post_constraints(p, nodes);

    SCCOptions scc_options;
    scc_options.fix_req = false;
    scc_options.prune_root = false;
    scc_options.prune_within = false;
    scc_options.prune_skip = true;
    p.post(CircuitSCC{nodes, false, scc_options});

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
                cout << s(nodes[current.raw_value]);
                current = s(nodes[current.raw_value]);
            }
            cout << "\n\n";
            return true;
        }},
        make_optional<ProofOptions>("circuit_prune_skip_test"));

    cout << stats;

    return EXIT_SUCCESS;
}
