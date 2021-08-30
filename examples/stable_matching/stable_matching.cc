/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/element.hh>
#include <gcs/constraints/table.hh>
#include <util/for_each.hh>

#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <random>
#include <string>
#include <vector>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::mt19937;
using std::pair;
using std::shuffle;
using std::stoi;
using std::string;
using std::to_string;
using std::vector;

using namespace std::literals::string_literals;

auto main(int argc, char * argv []) -> int
{
    Problem p{ Proof{ "stable_matching.opb", "stable_matching.veripb" } };

    unsigned size = 10;
    bool use_table = false;
    unsigned seed = 0;
    const string usage = " [ size ] [ table false|true ] [ seed ]";

    if (argc > 4) {
        cerr << "Usage: " << argv[0] << usage << endl;
        return EXIT_FAILURE;
    }

    if (argc >= 2)
        size = stoi(argv[1]);

    if (argc >= 3) {
        if (argv[2] == "true"s)
            use_table = true;
        else if (argv[2] == "false"s)
            use_table = false;
        else {
            cerr << "Usage: " << argv[0] << usage << endl;
            return EXIT_FAILURE;
        }
    }

    if (argc >= 4)
        seed = stoi(argv[3]);

    vector<IntegerVariableID> left, right;
    for (unsigned i = 0 ; i < size ; ++i) {
        left.push_back(p.create_integer_variable(0_i, Integer(size - 1), "left" + to_string(i)));
        right.push_back(p.create_integer_variable(0_i, Integer(size - 1), "right" + to_string(i)));
    }

    p.branch_on(left);

    mt19937 rand;
    rand.seed(seed);
    vector<vector<Integer> > left_prefs(size), right_prefs(size);
    for (auto & l : left_prefs) {
        for (Integer i{ 0 } ; i < Integer{ size } ; ++i)
            l.push_back(i);
        shuffle(l.begin(), l.end(), rand);
    }

    for (auto & r : right_prefs) {
        for (Integer i{ 0 } ; i < Integer{ size } ; ++i)
            r.push_back(i);
        shuffle(r.begin(), r.end(), rand);
    }

    vector<vector<unsigned> > left_ranks(size, vector<unsigned>(size)), right_ranks(size, vector<unsigned>(size));
    for (unsigned l = 0 ; l < size ; ++l)
        for (unsigned i = 0 ; i < size ; ++i)
            left_ranks[l][left_prefs[l][i].raw_value] = i;

    for (unsigned r = 0 ; r < size ; ++r)
        for (unsigned i = 0 ; i < size ; ++i)
            right_ranks[r][right_prefs[r][i].raw_value] = i;

    if (use_table) {
        // See Ian P. Gent, Robert W. Irving, David F. Manlove, Patrick Prosser, Barbara M. Smith:
        // A Constraint Programming Approach to the Stable Marriage Problem. CP 2001: 225-239
        for (Integer l{ 0 } ; l < Integer{ size } ; ++l) {
            for (Integer r{ 0 } ; r < Integer{ size } ; ++r) {
                // l -> left_prefs[l_gets] && r -> right_prefs[r_gets] is OK if...
                vector<IntegerVariableID> vars{ left[l.raw_value], right[r.raw_value] };
                vector<vector<Integer> > tuples;
                for (Integer l_gets{ 0 } ; l_gets < Integer{ size } ; ++l_gets) {
                    for (Integer r_gets{ 0 } ; r_gets < Integer{ size } ; ++r_gets) {
                        if (left_prefs[l.raw_value][l_gets.raw_value] == r && right_prefs[r.raw_value][r_gets.raw_value] == l) {
                            // state A
                            tuples.emplace_back(vector{ l_gets, r_gets });
                        }
                        else if (left_prefs[l.raw_value][l_gets.raw_value] == r && right_prefs[r.raw_value][r_gets.raw_value] != l) {
                            // state I
                        }
                        else if (left_prefs[l.raw_value][l_gets.raw_value] != r && right_prefs[r.raw_value][r_gets.raw_value] == l) {
                            // state I
                        }
                        else if (l_gets.raw_value > left_ranks[l.raw_value][r.raw_value] && r_gets.raw_value > right_ranks[r.raw_value][l.raw_value]) {
                            // state B
                        }
                        else {
                            // state S
                            tuples.emplace_back(vector{ l_gets, r_gets });
                        }
                    }
                }
                p.post(Table{ move(vars), move(tuples) });
            }
        }
    }
    else {
        for (unsigned l = 0 ; l < size ; ++l) {
            for (unsigned l_pref = 0 ; l_pref < size ; ++l_pref) {
                auto link = p.create_integer_variable(0_i, 1_i);
                p.post(EqualsIff{ left[l], constant_variable(Integer(l_pref)), link == 1_i });
                p.post(EqualsIff{ right[left_prefs[l][l_pref].raw_value], constant_variable(Integer(right_ranks[left_prefs[l][l_pref].raw_value][l])), link == 1_i });
            }
        }

        for (unsigned l = 0 ; l < size ; ++l) {
            for (unsigned r = 0 ; r < size ; ++r) {
                auto cond = p.create_integer_variable(0_i, 1_i);
                p.post(GreaterThanIff{ left[l], constant_variable(Integer(left_ranks[l][r])), cond == 1_i });
                p.post(LessThanIf{ right[r], constant_variable(Integer(right_ranks[r][l])), cond == 1_i });
            }
        }

        for (unsigned r = 0 ; r < size ; ++r) {
            for (unsigned l = 0 ; l < size ; ++l) {
                auto cond = p.create_integer_variable(0_i, 1_i);
                p.post(GreaterThanIff{ right[r], constant_variable(Integer(right_ranks[r][l])), cond == 1_i });
                p.post(LessThanIf{ left[l], constant_variable(Integer(left_ranks[l][r])), cond == 1_i });
            }
        }
    }

    auto stats = solve(p, [&] (const State & state) -> bool {
            for_each_with_index(left, [&] (IntegerVariableID l, auto index) {
                    cout << index << ":";
                    for (auto & pref : left_prefs[index]) {
                        cout << " " << pref;
                        if (left_prefs[index][state(l).raw_value] == pref)
                            cout << "*";
                        else
                            cout << " ";
                    }
                    cout << endl;
                });
            cout << endl;

            for_each_with_index(right, [&] (IntegerVariableID r, auto index) {
                    cout << index << ":";
                    for (auto & pref : right_prefs[index]) {
                        cout << " " << pref;
                        if (right_prefs[index][state(r).raw_value] == pref)
                            cout << "*";
                        else
                            cout << " ";
                    }
                    cout << endl;
                });
            cout << endl;

            cout << endl;

            return true;
            });

    cout << stats;

    return EXIT_SUCCESS;
}

