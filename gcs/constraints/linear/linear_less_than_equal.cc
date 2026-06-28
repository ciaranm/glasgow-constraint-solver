#include <gcs/constraints/linear/linear_less_than_equal.hh>

using namespace gcs;
using namespace gcs::innards;

LinearLessThanEqual::LinearLessThanEqual(WeightedSum coeff_vars, Integer value, std::optional<std::size_t> incremental_threshold) :
    ReifiedLinearInequality(move(coeff_vars), value, reif::MustHold{}, incremental_threshold)
{
}

LinearLessThanEqualIf::LinearLessThanEqualIf(WeightedSum coeff_vars, Integer value, IntegerVariableCondition cond) :
    ReifiedLinearInequality(move(coeff_vars), value, reif::If{cond})
{
}

LinearLessThanEqualIff::LinearLessThanEqualIff(WeightedSum coeff_vars, Integer value, IntegerVariableCondition cond) :
    ReifiedLinearInequality(move(coeff_vars), value, reif::Iff{cond})
{
}
