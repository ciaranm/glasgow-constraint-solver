#include <gcs/constraints/linear/linear_greater_than_equal.hh>

using namespace gcs;
using namespace gcs::innards;

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
    ReifiedLinearInequality(move(negate(coeff_vars)), -value, reif::MustHold{})
{
}

LinearGreaterThanEqualIf::LinearGreaterThanEqualIf(WeightedSum coeff_vars, Integer value, IntegerVariableCondition cond) :
    ReifiedLinearInequality(move(negate(coeff_vars)), -value, reif::If{cond})
{
}

LinearGreaterThanEqualIff::LinearGreaterThanEqualIff(WeightedSum coeff_vars, Integer value, IntegerVariableCondition cond) :
    ReifiedLinearInequality(move(negate(coeff_vars)), -value, reif::Iff{cond})
{
}
