#include <gcs/constraints/smart_table.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <gcs/extensional.hh>
#include <gcs/smart_entry.hh>
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
    int n = 10;
    Problem p;
    auto x = p.create_integer_variable_vector(n, 1_i, Integer{n}, "x");
    auto y = p.create_integer_variable_vector(n, 1_i, Integer{n}, "y");

    SmartTuples tuples;

    for(int i = 0; i < n; ++i) {
        vector<SmartEntry> tuple;
        for(int j = 0; j < i + 1; ++j) {
            if(j < i) {
                tuple.emplace_back(EqualsVar{x[j], y[j]});
            } else if (j == i) {
                tuple.emplace_back(GreaterThanVar{x[j], y[j]});
            }
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
                                        for(const auto & var : x) {
                                            cout << s(var) << " ";
                                        }
                                        cout << "]" << endl;
                                        cout << "y = [ ";
                                        for(const auto & var : y) {
                                            cout << s(var) << " ";
                                        }
                                        cout << "]" << endl;
                                        return false;
                                    }}
                            /*ProofOptions{"lex_table.opb", "lex_table.veripb"}*/ );

    cout << stats;

    return EXIT_SUCCESS;
}
