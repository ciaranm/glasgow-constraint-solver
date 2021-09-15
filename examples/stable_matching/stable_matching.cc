/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/element.hh>
#include <gcs/constraints/table.hh>
#include <util/for_each.hh>

#include <algorithm>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <random>
#include <string>
#include <vector>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::function;
using std::mt19937;
using std::nullopt;
using std::optional;
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
    unsigned dimensions = 2;
    bool use_table = false;
    unsigned seed = 0;
    const string usage = " [ size ] [ dimensions ] [ table false|true ] [ seed ]";

    if (argc > 5) {
        cerr << "Usage: " << argv[0] << usage << endl;
        return EXIT_FAILURE;
    }

    if (argc >= 2)
        size = stoi(argv[1]);

    if (argc >= 3)
        dimensions = stoi(argv[2]);

    if (argc >= 4) {
        if (argv[3] == "true"s)
            use_table = true;
        else if (argv[3] == "false"s)
            use_table = false;
        else {
            cerr << "Usage: " << argv[0] << usage << endl;
            return EXIT_FAILURE;
        }
    }

    if (argc >= 5)
        seed = stoi(argv[4]);

    vector<pair<int, int> > pairings;
    for (unsigned d1 = 0 ; d1 < dimensions ; ++d1)
        for (unsigned d2 = d1 + 1 ; d2 < dimensions ; ++d2)
            pairings.emplace_back(d1, d2);

    vector<vector<IntegerVariableID> > allocations{ pairings.size() * 2 };
    for_each_with_index(pairings, [&] (auto d, auto dx) {
        auto [ d1, d2 ] = d;
        for (unsigned i = 0 ; i < size ; ++i) {
            allocations[dx * 2].push_back(p.create_integer_variable(0_i, Integer(size - 1), "a" + to_string(d1) + "_" + to_string(d2) + "_" + to_string(i)));
            allocations[dx * 2 + 1].push_back(p.create_integer_variable(0_i, Integer(size - 1), "a" + to_string(d2) + "_" + to_string(d1) + "_" + to_string(i)));
        }
    });

    vector<IntegerVariableID> branch_vars;
    for_each_with_index(pairings, [&] (auto, auto dx) {
        for (unsigned i = 0 ; i < size ; ++i)
            branch_vars.push_back(allocations[dx * 2][i]);
    });

    p.branch_on(branch_vars);

    mt19937 rand;
    rand.seed(seed);
    vector<vector<vector<Integer> > > prefs{ pairings.size() * 2, vector<vector<Integer> >{ size, vector<Integer> { } } };

    auto make_prefs = [&] (vector<vector<Integer> > & p) {
        for (auto & l : p) {
            for (Integer i{ 0 } ; i < Integer{ size } ; ++i)
                l.push_back(i);
            shuffle(l.begin(), l.end(), rand);
        }
    };

    for_each_with_index(pairings, [&] (auto, auto dx) {
        make_prefs(prefs[dx * 2]);
        make_prefs(prefs[dx * 2 + 1]);
    });

    vector<vector<vector<unsigned> > > ranks{ pairings.size() * 2, vector<vector<unsigned> >{ size, vector<unsigned>(size, 0) } };

    auto make_ranks = [&] (vector<vector<unsigned> > & r, vector<vector<Integer> > & p) {
        for (unsigned l = 0 ; l < size ; ++l)
            for (unsigned i = 0 ; i < size ; ++i)
                r[l][p[l][i].raw_value] = i;
    };

    for_each_with_index(pairings, [&] (auto, auto dx) {
        make_ranks(ranks[dx * 2], prefs[dx * 2]);
        make_ranks(ranks[dx * 2 + 1], prefs[dx * 2 + 1]);
    });

    if (use_table) {
        auto impose = [&] (
                vector<IntegerVariableID> & left,
                vector<IntegerVariableID> & right,
                vector<vector<Integer> > & left_prefs,
                vector<vector<Integer> > & right_prefs,
                vector<vector<unsigned> > & left_ranks,
                vector<vector<unsigned> > & right_ranks
                ) {
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
        };

        for_each_with_index(pairings, [&] (auto, auto dx) {
            impose(allocations[dx * 2], allocations[dx * 2 + 1], prefs[dx * 2], prefs[dx * 2 + 1], ranks[dx * 2], ranks[dx * 2 + 1]);
        });
    }
    else {
        auto impose = [&] (
                vector<IntegerVariableID> & left,
                vector<IntegerVariableID> & right,
                vector<vector<Integer> > & left_prefs,
                vector<vector<Integer> > &,
                vector<vector<unsigned> > & left_ranks,
                vector<vector<unsigned> > & right_ranks
                ) {
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
        };

        for_each_with_index(pairings, [&] (auto, auto dx) {
            impose(allocations[dx * 2], allocations[dx * 2 + 1], prefs[dx * 2], prefs[dx * 2 + 1], ranks[dx * 2], ranks[dx * 2 + 1]);
        });
    }

    auto link = [&] (
            vector<IntegerVariableID> & left_to_right,
            vector<IntegerVariableID> & right_to_top,
            vector<IntegerVariableID> & left_to_top,
            vector<vector<Integer> > & left_prefs_over_right,
            vector<vector<Integer> > & right_prefs_over_top,
            vector<vector<Integer> > & left_prefs_over_top
            ) {
        for (unsigned l_idx = 0 ; l_idx < size ; ++l_idx) {
            auto l_goes_to_r = p.create_integer_variable(0_i, Integer(size - 1));
            vector<IntegerVariableID> left_prefs_over_right_consts;
            for (auto & p : left_prefs_over_right[l_idx])
                left_prefs_over_right_consts.push_back(constant_variable(p));
            p.post(Element{ l_goes_to_r, left_to_right[l_idx], left_prefs_over_right_consts });

            auto l_goes_to_r_goes_to_t = p.create_integer_variable(0_i, Integer(size - 1));
            auto r_goes_to_t = p.create_integer_variable(0_i, Integer(size - 1));
            p.post(Element{ r_goes_to_t, l_goes_to_r, right_to_top });
            vector<IntegerVariableID> right_prefs_over_top_vars;
            for (unsigned r = 0 ; r < size ; ++r)
                right_prefs_over_top_vars.push_back(p.create_integer_variable(0_i, Integer(size - 1)));
            for (unsigned r = 0 ; r < size ; ++r)
                for (unsigned s = 0 ; s < size ; ++s)
                    p.post(EqualsIf{ right_prefs_over_top_vars[r], constant_variable(right_prefs_over_top[s][r]), l_goes_to_r == Integer(s) });
            p.post(Element{ l_goes_to_r_goes_to_t, r_goes_to_t, right_prefs_over_top_vars });

            auto l_goes_to_t = p.create_integer_variable(0_i, Integer(size - 1));
            vector<IntegerVariableID> left_prefs_over_top_consts;
            for (auto & p : left_prefs_over_top[l_idx])
                left_prefs_over_top_consts.push_back(constant_variable(p));
            p.post(Element{ l_goes_to_t, left_to_top[l_idx], left_prefs_over_top_consts });

            p.post(Equals{ l_goes_to_t, l_goes_to_r_goes_to_t });
        };
    };

    for (auto & p1 : pairings)
        for (auto & p2 : pairings)
            if (p1.second == p2.first)
                link(allocations[p1.first * 2], allocations[p1.second * 2], allocations[p2.second * 2],
                        prefs[p1.first * 2], prefs[p1.second * 2], prefs[p2.second * 2]);

    unsigned n_solution = 0;
    auto stats = solve(p, [&] (const State & state) -> bool {
            ++n_solution;
            cout << "solution " << n_solution << endl << endl;

            auto show = [&] (
                    vector<IntegerVariableID> & left,
                    vector<IntegerVariableID> & right,
                    vector<vector<Integer> > & left_prefs,
                    vector<vector<Integer> > & right_prefs) {
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
            };

            for_each_with_index(pairings, [&] (auto d, auto dx) {
                auto [ d1, d2 ] = d;
                cout << "subproblem " << dx << " between " << d1 << " and " << d2 << endl;
                show(allocations[dx * 2], allocations[dx * 2 + 1], prefs[dx * 2], prefs[dx * 2 + 1]);
            });

            cout << endl;

            return true;
    });

    cout << stats;

    return EXIT_SUCCESS;
}

