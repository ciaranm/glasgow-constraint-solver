#include <gcs/constraints/circuit.hh>
#include <gcs/constraints/in.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <iostream>

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
    p.post(In{nodes[0], {2_i, 3_i}});
    p.post(In{nodes[1], {0_i, 7_i, 8_i}});
    p.post(In{nodes[2], {0_i, 3_i}});
    p.post(In{nodes[3], {5_i, 2_i, 0_i}});
    p.post(In{nodes[4], {5_i, 6_i}});
    p.post(In{nodes[5], {4_i, 6_i}});
    p.post(In{nodes[6], {4_i, 5_i}});
    p.post(In{nodes[7], {1_i, 8_i}});
    p.post(In{nodes[7], {1_i, 7_i}});
}
auto main(int, char *[]) -> int
{
    Problem p;
    auto nodes = p.create_integer_variable_vector(9, 0_i, 8_i);

    post_constraints(p, nodes);

    p.post(CircuitSCC{nodes});

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
        make_optional<ProofOptions>("scc_multiple_sccs.opb", "scc_multiple_sccs.veripb"));

    cout << stats;

    return EXIT_SUCCESS;
}