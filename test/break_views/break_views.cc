

#include <gcs/constraints/comparison.hh>
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

auto main(int, char *[]) -> int
{
    Problem p;
    auto y = p.create_integer_variable(-4_i, 3_i);
    auto x = p.create_integer_variable(-8_i, 7_i);
    p.post(GreaterThanEqual{y, -2_c});
    p.post(GreaterThanEqual{x, y + 3_i});
    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState &) -> bool {
                cout << "Solution:" << endl;
                return true;
            },
        },
        make_optional<ProofOptions>("break_views.opb", "break_views.pbp"));

    cout << stats;

    return EXIT_SUCCESS;
}
