

#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <gcs/constraints/smart_table.hh>

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
    auto x = p.create_integer_variable(-2_i, 8_i);
    auto y = p.create_integer_variable(-2_i, 4_i);
    auto tuples = SmartTuples{{LessThanVar{y, x - 3_i}}};
    p.post(SmartTable{{x, y}, tuples});
    auto stats = solve_with(p,
                            SolveCallbacks{
                                    .solution = [&](const CurrentState &s) -> bool {
                                        cout << "Solution: x = " << s(x) << "y =" << s(y) << endl;
                                        return true;
                                    },
                            },
                            make_optional<ProofOptions>("break_table_with_constants.opb",
                                                        "break_table_with_constants.veripb"));

    cout << stats;

    system("veripb --trace --useColor break_table_with_constants.opb break_table_with_constants.veripb");

    return EXIT_SUCCESS;
}
