#include <gcs/constraints/circuit/circuit.hh>
#include <gcs/constraints/in.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <iostream>
#include <string>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::make_optional;
using std::string;
using std::vector;

auto post_constraints(Problem & p, vector<IntegerVariableID> & nodes)
{
    // // From paper:
    //    p.post(In{nodes[0], {1_i, 4_i, 5_i}});
    //    p.post(In{nodes[1], {2_i, 3_i}});
    //    p.post(In{nodes[2], {0_i}});
    //    p.post(In{nodes[3], {2_i}});
    //    p.post(In{nodes[4], {1_i, 3_i}});
    //    p.post(In{nodes[5], {0_i, 6_i}});
    //    p.post(In{nodes[6], {3_i, 4_i}});

    // Messing about:
    //    p.post(In{nodes[0], {1_i, 2_i, 4_i, 5_i}});
    //    p.post(In{nodes[1], {0_i, 1_i, 2_i, 3_i, 6_i}});
    //    p.post(In{nodes[2], {0_i, 1_i, 2_i, 3_i, 4_i, 5_i, 6_i}});
    //    p.post(In{nodes[3], {0_i, 2_i, 3_i, 4_i, 5_i}});
    //    p.post(In{nodes[4], {0_i, 1_i, 2_i, 3_i, 4_i}});
    //    p.post(In{nodes[5], {0_i, 1_i, 2_i, 4_i, 6_i}});
    //    p.post(In{nodes[6], {0_i, 3_i, 4_i, 5_i, 6_i}});
}
auto main(int argc, char * argv[]) -> int
{
    Problem p1;
    auto nodes1 = p1.create_integer_variable_vector(7, 0_i, 6_i);

    post_constraints(p1, nodes1);

    p1.post(CircuitPrevent{nodes1});
    cout << "\nPREVENT:"
         << "\n----------" << endl;
    auto stats1 = solve_with(p1,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                //                for (const auto & v : nodes1) {
                //                    cout << s(v) << " ";
                //                }
                //                cout << endl;
                //                cout << 0 << " -> " << s(nodes1[0]);
                //                auto current = s(nodes1[0]);
                //                while (current != 0_i) {
                //                    cout << " -> ";
                //                    cout << s(nodes1[current.raw_value]);
                //                    current = s(nodes1[current.raw_value]);
                //                }
                //                cout << "\n\n";
                return true;
            }} /*,make_optional<ProofOptions>("tiny_circuit.opb", "tiny_circuit.veripb")*/);

    cout << stats1;

    Problem p2;
    auto nodes2 = p2.create_integer_variable_vector(7, 0_i, 6_i);

    post_constraints(p2, nodes2);

    p2.post(CircuitSCC{nodes2});
    cout << "\nSCC"
         << "\n----------" << endl;
    auto stats2 = solve_with(p2,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                //                for (const auto & v : nodes2) {
                //                    cout << s(v) << " ";
                //                }
                //                cout << endl;
                //                cout << 0 << " -> " << s(nodes2[0]);
                //                auto current = s(nodes2[0]);
                //                while (current != 0_i) {
                //                    cout << " -> ";
                //                    cout << s(nodes2[current.raw_value]);
                //                    current = s(nodes2[current.raw_value]);
                //                }
                //                cout << "\n\n";
                return true;
            }} /*,make_optional<ProofOptions>("tiny_circuit.opb", "tiny_circuit.veripb")*/);

    cout << stats2;
    return EXIT_SUCCESS;
}
