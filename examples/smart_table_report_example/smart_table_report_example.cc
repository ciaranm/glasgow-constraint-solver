#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/smart_table.hh>
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


    Problem p;

    auto x1 = p.create_integer_variable(1_i, 3_i, "x1");
    auto x2 = p.create_integer_variable(1_i, 3_i, "x2");
    auto x3 = p.create_integer_variable(1_i, 3_i, "x3");
    auto tuples = SmartTuples{
            {LessThanVar{x1, x2 - 3_i}, InSet{x1, {1_i, 2_i}}, EqualsValue{x3, 3_i}},
             {EqualsVar{x1, x2}, NotEqualsValue{x1, 1_i}, GreaterThanEqualVar{x2 - 2_i, x3}
             }};
    p.post(SmartTable{{x1, x2, x3}, tuples});

    //    vector<SmartEntry> tuple;
    //    for(int i = 0; i < 3; i++) {
    //        tuple.emplace_back(LessThanVar{x[i], x[i+1]});
    //    }
    //    x.emplace_back(y);
    //    p.post(SmartTable{x, {tuple}});

    auto stats = solve_with(p,
                            SolveCallbacks{
                                    .solution = [&](const CurrentState & s) -> bool {
                                        cout << "x1 = " << s(x1) << " x2 = " << s(x2) << " x3 = " << s(x3) << endl;
                                        return true;
                                    }},
                            ProofOptions{"smart_table_report_example.opb", "smart_table_report_example.veripb"});

    cout << stats;

    return EXIT_SUCCESS;
}
