/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/arithmetic.hh>
#include <gcs/detail/propagators.hh>
#include <gcs/detail/state.hh>

#include <cmath>
#include <tuple>
#include <vector>

using namespace gcs;

using std::llroundl;
using std::move;
using std::pow;
using std::vector;

template <ArithmeticOperator op_>
Arithmetic<op_>::Arithmetic(const IntegerVariableID v1, const IntegerVariableID v2, const IntegerVariableID result) :
    _v1(v1),
    _v2(v2),
    _result(result)
{
}

template <ArithmeticOperator op_>
auto Arithmetic<op_>::install(Propagators & propagators, const State & initial_state) && -> void
{
    bool v2_zero_is_ok = (op_ != ArithmeticOperator::Div && op_ != ArithmeticOperator::Mod);

    vector<vector<Integer>> permitted;

    initial_state.for_each_value(_v1, [&](Integer v1) {
        initial_state.for_each_value(_v2, [&](Integer v2) {
            if ((v2_zero_is_ok || v2 != 0_i) && initial_state.in_domain(_v2, v2)) {
                Integer r = 0_i;
                switch (op_) {
                case ArithmeticOperator::Plus: r = v1 + v2; break;
                case ArithmeticOperator::Minus: r = v1 - v2; break;
                case ArithmeticOperator::Times: r = v1 * v2; break;
                case ArithmeticOperator::Div: r = v1 / v2; break;
                case ArithmeticOperator::Mod: r = v1 % v2; break;
                case ArithmeticOperator::Power: r = Integer{llroundl(pow(v1.raw_value, v2.raw_value))}; break;
                }
                if (initial_state.in_domain(_result, r))
                    permitted.push_back(vector{v1, v2, r});
            }
        });
    });

    propagators.define_and_install_table(initial_state, vector{_v1, _v2, _result}, move(permitted), "arithmetic");
}

template <ArithmeticOperator op_>
auto Arithmetic<op_>::describe_for_proof() -> std::string
{
    return "arithmetic";
}

namespace gcs
{
    template class Arithmetic<ArithmeticOperator::Plus>;
    template class Arithmetic<ArithmeticOperator::Minus>;
    template class Arithmetic<ArithmeticOperator::Times>;
    template class Arithmetic<ArithmeticOperator::Div>;
    template class Arithmetic<ArithmeticOperator::Mod>;
    template class Arithmetic<ArithmeticOperator::Power>;
}
