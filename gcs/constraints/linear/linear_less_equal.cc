#include <gcs/constraints/linear/linear_less_equal.hh>

using namespace gcs;
using namespace gcs::innards;

LinearLessEqual::LinearLessEqual(WeightedSum coeff_vars, Integer value) :
    LinearInequalityIff(move(coeff_vars), value, TrueLiteral{})
{
}

LinearLessEqualIff::LinearLessEqualIff(WeightedSum coeff_vars, Integer value, Literal cond) :
    LinearInequalityIff(move(coeff_vars), value, cond)
{
}
