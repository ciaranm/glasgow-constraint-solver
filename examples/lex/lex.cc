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
    int n = 4;
    Problem p;
    auto x = p.create_integer_variable_vector(n, 0_i, 10_i, "x");
    auto y = p.create_integer_variable_vector(n, 0_i, 10_i, "y");

    p.post(Equals(y[0], 5_c));
    p.post(Equals(y[1], 2_c));
    p.post(Equals(y[2], 10_c));
    p.post(Equals(y[3], 5_c));

    p.post(Equals(x[0], 5_c));
    p.post(Equals(x[1], 2_c));
    // Only option for x[2] is 10, since it comes lexicographically first
    p.post(Equals(x[3], 6_c));

    // Smart table representation of the Lex constraint
    // As given in "The Smart Table Constraint" Mairy, J. B., Deville, Y., & Lecoutre, C. (2015)
    SmartTuples tuples;

    for (int i = 0; i < n; ++i) {
        vector<SmartEntry> tuple;
        for (int j = 0; j < i + 1; ++j) {
            if (j < i)
                tuple.emplace_back(SmartTable::equals(x[j], y[j]));
            else if (j == i)
                tuple.emplace_back(SmartTable::greater_than(x[j], y[j]));
        }
        tuples.emplace_back(tuple);
    }

    auto all_vars = x;
    all_vars.insert(all_vars.end(), y.begin(), y.end());

    p.post(SmartTable{all_vars, tuples});

    auto stats = solve_with(p,
        SolveCallbacks{
            .solution = [&](const CurrentState & s) -> bool {
                cout << "x = [ ";
                for (const auto & var : x) {
                    cout << s(var) << " ";
                }
                cout << "]" << endl;
                cout << "y = [ ";
                for (const auto & var : y) {
                    cout << s(var) << " ";
                }
                cout << "]\n"
                     << endl;
                return true;
            }},
        ProofOptions{"lex.opb", "lex.veripb"});

    cout << stats;

    return EXIT_SUCCESS;
}
