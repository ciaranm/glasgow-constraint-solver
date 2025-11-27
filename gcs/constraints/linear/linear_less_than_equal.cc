#include <gcs/constraints/linear/linear_less_than_equal.hh>

using namespace gcs;
using namespace gcs::innards;

LinearLessThanEqual::LinearLessThanEqual(WeightedSum coeff_vars, Integer value) :
    LinearInequalityIff(move(coeff_vars), value, TrueLiteral{})
{
}

LinearLessThanEqualIf::LinearLessThanEqualIf(WeightedSum coeff_vars, Integer value, Literal cond) :
    LinearInequalityIf(move(coeff_vars), value, cond)
{
}

LinearLessThanEqualIff::LinearLessThanEqualIff(WeightedSum coeff_vars, Integer value, Literal cond) :
    LinearInequalityIff(move(coeff_vars), value, cond)
{
}
