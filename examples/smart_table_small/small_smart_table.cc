#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/smart_table.hh>
#include <gcs/extensional.hh>
#include <gcs/problem.hh>
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

    Problem p;

    auto x1 = p.create_integer_variable(-2_i, 3_i, "x1");
    auto x2 = p.create_integer_variable(-2_i, 32_i, "x2");
    auto x3 = p.create_integer_variable(-2_i, 64_i, "x3");
    auto tuples = SmartTuples{
        {SmartTable::less_than(x1, x2 - 3_i), SmartTable::in_set(x1, {1_i, 2_i}), SmartTable::equals(x3, 3_i)},
        {SmartTable::equals(x1, x2), SmartTable::not_equals(x1, 1_i), SmartTable::greater_than_equal(x2, x3 - 8_i)}};
    p.post(SmartTable{{x1, x2, x3}, tuples});
    
    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                cout << "x1 = " << s(x1) << " x2 = " << s(x2) << " x3 = " << s(x3) << endl;
                return true;
            }},
        ProofOptions{"smart_table_small.opb", "smart_table_small.veripb"});

    cout << stats;

    return EXIT_SUCCESS;
}
