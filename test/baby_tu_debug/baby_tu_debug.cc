#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <iostream>
#include <string>

#include <boost/program_options.hpp>
#include <gcs/constraints/baby_tu.hh>
#include <gcs/constraints/not_equals.hh>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::make_optional;
using std::nullopt;
using std::string;
using std::vector;

auto main(int argc, char * argv[]) -> int
{

    //    auto n = options_vars["n"].as<int>();

    Problem p;
    auto vars = p.create_integer_variable_vector(10, 1_i, 20_i, "x");

    for (int i = 0; i < 9; i++) {
        p.post(BabyTU{vars[i], vars[i + 1]});
    }

    //    p.post(NotEquals(vars[3], 4_c));
    //    p.post(NotEquals(vars[2], 1_c));

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                //                cout << "Solution:" << endl;
                //                for (const auto & v : vars) {
                //                    cout << s(v) << " ";
                //                }
                //                cout << endl;
                return true;
            },
        },
        make_optional<ProofOptions>("baby_tu_debug"));

    cout << stats;

    return EXIT_SUCCESS;
}
