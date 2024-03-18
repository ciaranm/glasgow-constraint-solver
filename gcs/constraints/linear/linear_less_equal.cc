#include <gcs/constraints/linear/linear_less_equal.hh>

using namespace gcs;

LinearLessEqual::LinearLessEqual(WeightedSum coeff_vars, Integer value) :
    LinearInequality(move(coeff_vars), value)
{
}
