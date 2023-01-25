#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <gcs/constraints/smart_table.hh>
#include <gcs/smart_entry.hh>
#include <gcs/exception.hh>
#include <cstdlib>
#include <vector>
#include <tuple>
#include <iostream>

using std::vector;
using std::pair;
using std::tuple;
using std::cout;

auto check_lex(vector<Integer>& x_sols, vector<Integer>& y_sols, bool or_equal=false) -> bool {
    if(x_sols.size() != y_sols.size()) cout << "Tuples not same length!";
    if(or_equal ?  x_sols[0] >= y_sols[0] : x_sols[0] > y_sols[0]) return true;
    if(or_equal ?  y_sols[0] >= x_sols[0] : y_sols[0] > x_sols[0]) return false;
    if(x_sols.size() == 1) return false;

    vector<Integer> x_sols_smaller = {x_sols.begin() + 1, x_sols.end()};
    vector<Integer> y_sols_smaller = {y_sols.begin() + 1, y_sols.end()};
    return check_lex(x_sols_smaller, y_sols_smaller);
}

auto run_lex_test(int length, vector<pair<int, int>> ranges, bool reverse=false) -> bool {
    vector<IntegerVariableID> x;
    vector<IntegerVariableID> y;

    Problem p;

    for(int i = 0; i < length; i++) {
        x.emplace_back(p.create_integer_variable(Integer(ranges[i].first), Integer(ranges[i].second)));
        y.emplace_back(p.create_integer_variable(Integer(ranges[i].first), Integer(ranges[i].second)));
    }
    SmartTuples tuples;

    for (int i = 0; i < length; ++i) {
        vector<SmartEntry> tuple;
        for (int j = 0; j < i + 1; ++j) {
            if (j < i) {
                tuple.emplace_back(EqualsVar{x[j], y[j]});
            }
            else if (j == i) {
                if(reverse)
                    tuple.emplace_back(LessThanEqualVar{x[j], y[j]});
                else
                    tuple.emplace_back(GreaterThanVar{x[j], y[j]});
            }
        }
        tuples.emplace_back(tuple);
    }

    auto all_vars = x;
    all_vars.insert(all_vars.end(), y.begin(), y.end());

    p.post(SmartTable{all_vars, tuples});

    bool lex_violated = false;
    solve_with(p,
        SolveCallbacks{
                .solution = [&](const CurrentState & s) -> bool {
                    vector<Integer> x_sols;
                    vector<Integer> y_sols;
                    for(int i = 0; i < length; ++i) {
                        x_sols.emplace_back(s(x[i]));
                        y_sols.emplace_back(s(y[i]));
                    }
                    lex_violated = lex_violated || (reverse ? (!check_lex(y_sols, x_sols, true)) : (!check_lex(x_sols, y_sols)));
                    return true;
                }},
        ProofOptions{"lex_table.opb", "lex_table.veripb"});

    return !lex_violated && (0 == system("veripb lex_table.opb lex_table.veripb"));
}

auto main(int, char *[]) -> int
{
    vector<pair<int, vector<pair<int, int>>>> data = {
            //Length    //Ranges
            {3,         {{1, 3}, {1, 2}, {2, 3}}},
            {3,         {{1, 2}, {1, 2}, {1, 2}}},
            {4,         {{-3, 0}, {1, 4}, {3, 3}, {3, 3}}},
            {4,         {{5, 5}, {2, 4}, {0, 4}, {1, 5}}},
            {5,         {{-1, 4}, {3, 6}, {2, 2}, {3, 3}, {3, 5}}},
            {5,         {{1, 1}, {2, 2}, {3, 3}, {4, 4}, {1, 10}}}
    };

    for (auto & [length, ranges] : data) {
        if(!run_lex_test(length, ranges, false))
            return EXIT_FAILURE;
        if(!run_lex_test(length, ranges, true))
            return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}