/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/constraints/linear_equality.hh>
#include <gcs/problem.hh>
#include <gcs/linear.hh>

using namespace gcs;

LinearEquality::LinearEquality(Linear && coeff_vars, Integer value) :
    _coeff_vars(move(coeff_vars)),
    _value(value)
{
}

auto LinearEquality::convert_to_low_level(LowLevelConstraintStore & p, const State &) && -> void
{
    sanitise_linear(_coeff_vars);

    // Use input as < constraint, create >= constraint to get equality
    Linear inv_coeff_vars;
    inv_coeff_vars.reserve(_coeff_vars.size());
    for (auto & [ c, v ] : _coeff_vars)
        inv_coeff_vars.emplace_back(-c, v);

    p.lin_le(move(inv_coeff_vars), -_value);
    p.lin_le(move(_coeff_vars), _value);
}

