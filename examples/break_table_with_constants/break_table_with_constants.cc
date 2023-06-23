

#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/smart_table.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <iostream>
#include <random>
#include <string>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::make_optional;
using std::mt19937;
using std::string;
using std::uniform_int_distribution;
using std::vector;

auto main(int, char *[]) -> int
{
    Problem p;
    mt19937 rng(0);
    uniform_int_distribution<> rand0_min(-130, -1);
    while (true) {

        auto l_x = rand0_min(rng);
        auto l_y = rand0_min(rng);
        auto x = p.create_integer_variable(Integer{l_x}, Integer{-l_x - 1});
        auto y = p.create_integer_variable(Integer{l_y}, Integer{-l_y - 1});
        cout << "l_x = " << l_x << "; u_x = " << -l_x - 1 << endl;
        cout << "l_y = " << l_y << "; u_y = " << -l_y - 1 << endl;
        uniform_int_distribution<> rand_in_range_y(l_y, -l_y - 1);
        auto l = rand_in_range_y(rng);
        auto tuples = SmartTuples{{GreaterThanEqualValue{y, Integer{l}}, GreaterThanVar{x, y}}};
        p.post(SmartTable{{x, y}, tuples});

        solve_with(p,
            SolveCallbacks{
                .solution = [&](const CurrentState &) -> bool {
                    //                                            cout << "Solution: x = " << s(x) << "y =" << s(y) << endl;
                    return false;
                },
            },
            make_optional<ProofOptions>("break_table_with_constants.opb",
                "break_table_with_constants.veripb"));

        if (system("veripb break_table_with_constants.opb break_table_with_constants.veripb") != 0) {
            return EXIT_FAILURE;
        }
    }

    return EXIT_SUCCESS;
}
