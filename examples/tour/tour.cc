#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <gcs/constraints/circuit.hh>
#include <vector>
#include <iostream>
#include "gcs/constraints/equals.hh"

using namespace gcs;
using std::vector;
using std::cout;
using std::endl;

auto main(int argc, char * argv[]) -> int
{
    int N = 7;
    Problem p = Problem{ProofOptions{"tour.opb", "tour.veripb"}};
    vector<IntegerVariableID> succ = p.create_integer_variable_vector(N, 0_i, Integer{N-1});

    p.post(NotEquals{succ[3], 4_c
    });

    p.post(NotEquals{succ[4], 2_c
    });

    p.post(Equals{succ[2], 5_c
    });
    p.post(Circuit{succ, true});

    auto stats = solve_with(p,
        SolveCallbacks{
        .solution = [&](const CurrentState & s) -> bool {

            for(const auto & v :succ) {
                cout << s(v) << " ";
            }
            cout << endl;
            cout << 0 << " -> " << s(succ[0]);
            auto current = s(succ[0]);
            while(current != 0_i) {
                cout << " -> ";
                cout << s(succ[current.raw_value]);
                current = s(succ[current.raw_value]);

            }
            cout << "\n\n";
            return true;
        }
    });

    cout << stats;

    return EXIT_SUCCESS;
}