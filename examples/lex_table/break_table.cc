#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/smart_table.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/extensional.hh>
#include <gcs/problem.hh>
#include <gcs/smart_entry.hh>
#include <gcs/solve.hh>
#include <iostream>
#include <vector>

using namespace gcs;

using std::cout;
using std::endl;
using std::make_optional;
using std::nullopt;
using std::vector;

auto main(int, char *[]) -> int
{

    // An example that breaks the Smart Table proofs if the extra inferences are not made.
    Problem p;
    auto x = p.create_integer_variable_vector(4, -2_i, 0_i, "x");

    auto y = p.create_integer_variable(0_i, 1_i, "y");

    // // Another option:
    //    auto x = p.create_integer_variable(-1_i, 3_i, "x");
    //    auto z = p.create_integer_variable(-1_i, 3_i, "z");
    //    auto y = p.create_integer_variable(-1_i, 3_i, "y");
    //    auto tuples = SmartTuples{
    //                        {NotEqualsVar{y, x}, InSet{y, {-1_i, 2_i, 3_i}}, InSet{z, {-1_i, 0_i, 1_i}}, GreaterThanVar{z, y}}
    //                        };
    //    p.post(SmartTable{{x, y, z}, tuples});

    vector<SmartEntry> tuple;
    for(int i = 0; i < 3; i++) {
        tuple.emplace_back(LessThanVar{x[i], x[i+1]});
    }
    x.emplace_back(y);
    p.post(SmartTable{x, {tuple}});

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
//                cout << "x = " << s(x) << " z = " << s(z) << " y = " << s(y) << endl;
                return true;
            }},
        ProofOptions{"break_table.opb", "break_table.veripb"});

    cout << stats;

    return EXIT_SUCCESS;
}
