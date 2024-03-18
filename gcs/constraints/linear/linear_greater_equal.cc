#include <gcs/constraints/linear/linear_greater_equal.hh>

using namespace gcs;

namespace
{
    auto negate(WeightedSum & coeff_vars) -> WeightedSum &
    {
        for (auto & [c, _] : coeff_vars.terms)
            c = -c;
        return coeff_vars;
    }
}

LinearGreaterThanEqual::LinearGreaterThanEqual(WeightedSum coeff_vars, Integer value) :
    LinearInequality(move(negate(coeff_vars)), -value)
{
}
