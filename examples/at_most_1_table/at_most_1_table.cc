#include <gcs/constraints/comparison.hh>
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
    int n = 3;

    Problem p;
    auto x = p.create_integer_variable_vector(n, 0_i, 3_i, "x");
    auto y = p.create_integer_variable(3_i, 3_i, "y");
    // Smart table representation of the AtMost1 constraint
    // As given in "The Smart Table Constraint" Mairy, J. B., Deville, Y., & Lecoutre, C. (2015)
    SmartTuples tuples;

    for (int i = 0; i < n; ++i) {
        vector<SmartEntry> tuple;
        for (int j = 0; j < n; ++j) {
            if (j != i) {
                tuple.emplace_back(SmartTable::not_equals(x[j], y));
            }
        }
        tuples.emplace_back(tuple);
    }

    auto all_vars = x;
    all_vars.emplace_back(y);

    p.post(SmartTable{all_vars, tuples});

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                cout << "x = [ ";
                for (const auto & var : x) {
                    cout << s(var) << " ";
                }
                cout << "]" << endl;
                return true;
            }},
        ProofOptions{"at_most_1_table.opb", "at_most_1_table.veripb"});

    cout << stats;

    return EXIT_SUCCESS;
}
