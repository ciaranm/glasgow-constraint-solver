#include <gcs/array_param.hh>
#include <gcs/problem.hh>

#include <vector>

// Corrected twins of the dangling_*.cc probes in this directory: the same
// operations, but against named objects that live long enough. This file is
// compiled with the same -Werror=dangling flags as the probes and must build
// cleanly, so that a failing probe means its annotation fired, rather than
// that the probe code never compiled in the first place.

auto valid_array_param_deref() -> int
{
    gcs::VectorArrayParam<int> param{{1, 2, 3}};
    const std::vector<int> & v = *param;
    return v[0];
}

auto valid_all_normal_variables() -> unsigned long long
{
    gcs::Problem problem;
    const auto & vars = problem.all_normal_variables();
    return vars.size();
}

auto valid_create_integer_variable() -> unsigned long long
{
    gcs::Problem problem;
    auto id = problem.create_integer_variable(gcs::Integer{1}, gcs::Integer{3});
    return id.index;
}
