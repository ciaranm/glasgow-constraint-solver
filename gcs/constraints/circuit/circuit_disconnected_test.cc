
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <iostream>
#include <string>

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

auto main(int, char *[]) -> int
{
    Problem p;

    auto x = p.create_integer_variable_vector(8, 0_i, 7_i);

    p.post(In{x[0], {1_i, 2_i, 3_i}});
    p.post(In{x[1], {3_i, 2_i}});
    p.post(In{x[2], {1_i, 3_i}});
    p.post(In{x[3], {2_i, 1_i}});

    p.post(In{x[4], {5_i, 6_i}});
    p.post(In{x[5], {7_i, 4_i}});
    p.post(In{x[6], {5_i, 7_i}});
    p.post(In{x[7], {4_i, 6_i}});

    p.post(CircuitSCC{x});
    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState &) -> bool {
                cout << "Solution:" << endl;
                return true;
            },
        },
        make_optional<ProofOptions>("circuit_disconnected_test.opb", "circuit_disconnected_test.pbp"));

    cout << stats;

    return EXIT_SUCCESS;
}
