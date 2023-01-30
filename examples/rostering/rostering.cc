#include <cstdlib>
#include <gcs/constraints/regular.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <iostream>
#include <optional>
#include <vector>

using namespace gcs;
using std::cout;
using std::endl;
using std::make_optional;
using std::vector;

auto main(int, char *[]) -> int
{
    Problem p;
    vector<IntegerVariableID> day;
    day.emplace_back(p.create_integer_variable(0_i, 3_i, "day0"));
    day.emplace_back(p.create_integer_variable({1_i, 3_i}, "day1"));
    day.emplace_back(p.create_integer_variable({0_i, 2_i, 3_i}, "day2"));
    day.emplace_back(p.create_integer_variable({0_i, 1_i, 3_i}, "day3"));
    day.emplace_back(p.create_integer_variable({0_i}, "day4"));

    // Regular constraint for the language given by 00*11*00* + 2*
    // 5 states 0..4, 3 possible values 0..2
    vector<vector<long>> transitions(7, vector<long>(4, -1));
    // Transitions
    transitions[0][0] = 1;
    transitions[0][1] = 2;
    transitions[0][2] = 3;
    transitions[0][3] = 0;

    transitions[1][0] = 1;
    transitions[1][3] = 4;

    transitions[2][1] = 2;
    transitions[2][3] = 5;

    transitions[3][2] = 3;
    transitions[3][3] = 6;

    transitions[4][3] = 4;
    transitions[4][0] = 1;
    transitions[4][1] = 2;

    transitions[5][3] = 5;
    transitions[5][1] = 2;
    transitions[5][2] = 3;

    transitions[6][3] = 6;
    transitions[6][2] = 3;
    transitions[6][0] = 1;

    auto regular = Regular{day, {0_i, 1_i, 2_i, 3_i}, 7, transitions, {0, 1, 2, 3, 4, 5, 6}};

    p.post(regular);

    auto stats = solve_with(p,
                            SolveCallbacks{
                                    .solution = [&](const CurrentState & s) -> bool {
                                        for (const auto & var : day) {
                                            cout << s(var);
                                        }
                                        cout << endl;
                                        return true;
                                    },
                            },
                            make_optional<ProofOptions>("regex.opb", "regex.veripb"));

    cout << stats;

    return EXIT_SUCCESS;
}