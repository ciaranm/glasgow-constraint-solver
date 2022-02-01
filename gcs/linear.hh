/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_LINEAR_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_LINEAR_HH

#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <utility>
#include <vector>

namespace gcs
{
    using CoefficientAndVariable = std::pair<Integer, IntegerVariableID>;
    using Linear = std::vector<CoefficientAndVariable>;
}

#endif
