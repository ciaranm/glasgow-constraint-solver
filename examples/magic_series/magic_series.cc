/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/linear_equality.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <util/for_each.hh>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <vector>

using namespace gcs;

using std::cerr;
using std::cout;
using std::endl;
using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::to_string;
using std::vector;

auto main(int, char * []) -> int
{
    int size = 300;
    Problem p; // { Proof{ "magic_series.opb", "magic_series.veripb" } };

    vector<IntegerVariableID> series;
    for (int v = 0 ; v != size ; ++v)
        series.push_back(p.create_integer_variable(0_i, Integer{ size - 1 }, "series" + to_string(v)));

    for (int i = 0 ; i < size ; ++i) {
        Linear coeff_vars;
        for (int j = 0 ; j < size ; ++j) {
            auto series_j_eq_i = p.create_integer_variable(0_i, 1_i);
            p.post(EqualsIff{ series[j], constant_variable(Integer{ i }), series_j_eq_i == 1_i });
            coeff_vars.emplace_back(1_i, series_j_eq_i);
        }

        coeff_vars.emplace_back(-1_i, series[i]);
        p.post(LinearEquality{ move(coeff_vars), 0_i });
    }

    Linear sum_s;
    for (auto & s : series)
        sum_s.emplace_back(1_i, s);
    p.post(LinearEquality{ move(sum_s), Integer{ size } });

//    Linear sum_mul_s;
//    for_each_with_index(series, [&] (IntegerVariableID s, auto idx) {
//            sum_mul_s.emplace_back(Integer(idx), s);
//            });
//    p.post(LinearEquality{ move(sum_mul_s), Integer{ size } });

    p.branch_on(series);

    auto stats = solve_with(p, SolveCallbacks{
            .solution = [&] (const State & s) -> bool {
                cout << "solution:";
                for (auto & v : series)
                    cout << " " << s(v);
                cout << endl;

                return true;
                },
            .guess = [&] (const State & state, IntegerVariableID var) -> vector<Literal> {
                return vector<Literal>{ var == state.lower_bound(var), var != state.lower_bound(var) };
            }
            });

    cout << stats;

    return EXIT_SUCCESS;
}

