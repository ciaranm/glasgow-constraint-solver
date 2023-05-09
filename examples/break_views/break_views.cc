

#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <gcs/constraints/comparison.hh>
#include <iostream>
#include <string>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::string;
using std::vector;
using std::make_optional;

auto main(int argc, char *argv[]) -> int {
    Problem p;
    auto y = p.create_integer_variable(-4_i, 3_i);
    auto x = p.create_integer_variable(-8_i, 7_i);
    p.post(GreaterThanEqual{y, -2_c});
    p.post(GreaterThanEqual{x, y+3_i});
    auto stats = solve_with(p,
                            SolveCallbacks{
                                    .solution = [&](const CurrentState &s) -> bool {
                                        cout << "Solution:" << endl;
                                        return true;
                                    },
                            },
                            make_optional<ProofOptions>("break_views.opb", "break_views.veripb"));

    cout << stats;

    return EXIT_SUCCESS;
}
