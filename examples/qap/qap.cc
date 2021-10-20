/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/arithmetic.hh>
#include <gcs/constraints/linear_equality.hh>
#include <gcs/constraints/element.hh>
#include <gcs/constraints/table.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <algorithm>
#include <array>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <vector>

using namespace gcs;

using std::array;
using std::cerr;
using std::cout;
using std::endl;
using std::flush;
using std::ifstream;
using std::getline;
using std::pair;
using std::string;
using std::to_string;
using std::vector;

auto main(int, char * []) -> int
{
    constexpr int size = 12;

    array<array<int, size>, size> weight_consts{
        array<int, size>{0,90,10,23,43,0,0,0,0,0,0,0},
        array<int, size>{90,0,0,0,0,88,0,0,0,0,0,0},
        array<int, size>{10,0,0,0,0,0,26,16,0,0,0,0},
        array<int, size>{23,0,0,0,0,0,0,0,0,0,0,0},
        array<int, size>{43,0,0,0,0,0,0,0,0,0,0,0},
        array<int, size>{0,88,0,0,0,0,0,0,1,0,0,0},
        array<int, size>{0,0,26,0,0,0,0,0,0,0,0,0},
        array<int, size>{0,0,16,0,0,0,0,0,0,96,0,0},
        array<int, size>{0,0,0,0,0,1,0,0,0,0,29,0},
        array<int, size>{0,0,0,0,0,0,0,96,0,0,0,37},
        array<int, size>{0,0,0,0,0,0,0,0,29,0,0,0},
        array<int, size>{0,0,0,0,0,0,0,0,0,37,0,0} };

    array<array<int, size>, size> distances_consts{
        array<int, size>{0,36,54,26,59,72,9,34,79,17,46,95},
        array<int, size>{36,0,73,35,90,58,30,78,35,44,79,36},
        array<int, size>{54,73,0,21,10,97,58,66,69,61,54,63},
        array<int, size>{26,35,21,0,93,12,46,40,37,48,68,85},
        array<int, size>{59,90,10,93,0,64,5,29,76,16,5,76},
        array<int, size>{72,58,97,12,64,0,96,55,38,54,0,34},
        array<int, size>{9,30,58,46,5,96,0,83,35,11,56,37},
        array<int, size>{34,78,66,40,29,55,83,0,44,12,15,80},
        array<int, size>{79,35,69,37,76,38,35,44,0,64,39,33},
        array<int, size>{17,44,61,48,16,54,11,12,64,0,70,86},
        array<int, size>{46,79,54,68,5,0,56,15,39,70,0,18},
        array<int, size>{95,36,63,85,76,34,37,80,33,86,18,0} };

    auto max_distance = 0;
    for (auto & d : distances_consts)
        for (auto & dd : d)
            if (dd > max_distance)
                max_distance = dd;

    auto max_weight = 0;
    for (auto & w : weight_consts)
        for (auto & ww : w)
            if (ww > max_weight)
                max_weight = ww;

    Problem p; // { Proof{ "qap.opb", "qap.veripb" } };

    vector<IntegerVariableID> weights;
    for (auto & w : weight_consts) {
        for (auto & ww : w)
            weights.push_back(constant_variable(Integer{ ww }));
    }

    vector<IntegerVariableID> xs;
    for (int i = 0 ; i < size ; ++i)
        xs.push_back(p.create_integer_variable(0_i, Integer{ size - 1 }));

    p.post(AllDifferent{ xs });

    vector<vector<Integer> > tuples;
    for (int i = 0 ; i < size ; ++i)
        for (int j = 0 ; j < size ; ++j)
            tuples.emplace_back(vector{ Integer{ i }, Integer{ j }, Integer{ distances_consts[i][j] } });

    Linear wcosts;
    for (int i = 0 ; i < size ; ++i) {
        for (int j = 0 ; j < size ; ++j) {
            auto d_xsi_xsj = p.create_integer_variable(0_i, Integer{ max_distance } + 1_i);
            vector<IntegerVariableID> vars{ xs[i], xs[j], d_xsi_xsj };
            auto tuples_copy = tuples;
            p.post(Table{ vars, move(tuples_copy) });

            wcosts.emplace_back(Integer{ weight_consts[i][j] }, d_xsi_xsj);
        }
    }

    auto cost = p.create_integer_variable(0_i, Integer{ size * size * max_weight * max_distance });
    wcosts.emplace_back(-1_i, cost);
    p.post(LinearEquality{ move(wcosts), 0_i });

    p.branch_on(xs);
    p.minimise(cost);

    unsigned long long nodes = 0;
    auto stats = solve_with(p, SolveCallbacks{
            .solution = [&] (const State & s) -> bool {
                cout << "cost: " << s(cost) << endl;
                return true;
            },
            .trace = [&] (const State &) -> bool {
                if (0 == (++nodes % 1000))
                    cerr << nodes << endl;
                return true;
            },
            .guess = [&] (const State & state, IntegerVariableID var) -> vector<Literal> {
                return vector<Literal>{ var == state.lower_bound(var), var != state.lower_bound(var) };
            }
            });

    cout << stats << endl;

    return EXIT_SUCCESS;
}

