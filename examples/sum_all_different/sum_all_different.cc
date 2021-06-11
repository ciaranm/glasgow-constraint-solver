/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <iostream>
#include <vector>

using namespace gcs;

using std::cout;
using std::endl;
using std::pair;
using std::vector;

auto main(int, char * []) -> int
{
    Problem p;

    vector<IntegerVariableID> xs;
    xs.push_back(p.allocate_integer_variable(1_i, 5_i));
    xs.push_back(p.allocate_integer_variable(1_i, 5_i));
    xs.push_back(p.allocate_integer_variable(1_i, 5_i));
    xs.push_back(p.allocate_integer_variable(1_i, 5_i));

    for (auto & x : xs)
        p.cnf({ x != 3_i });

    p.all_different(xs);

    vector<pair<Integer, IntegerVariableID> > xs_le_14;
    for (auto & x : xs)
        xs_le_14.emplace_back(Integer{ 1 }, x);
    p.lin_le(xs_le_14, Integer{ 14 });

    vector<pair<Integer, IntegerVariableID> > xs_ge_14;
    for (auto & x : xs)
        xs_ge_14.emplace_back(Integer{ -1 }, x);
    p.lin_le(xs_ge_14, Integer{ -14 });

    auto stats = solve(p, [&] (const State & s) -> bool {
            cout << "[";
            for (auto & x : xs)
                cout << " " << s.value_of(x)->raw_value;
            cout << " ]" << endl;

            return true;
            });

    cout << "recursions: " << stats.recursions << endl;
    cout << "max depth:  " << stats.max_depth << endl;

    return EXIT_SUCCESS;
}

