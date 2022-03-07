/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_LINEAR_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_LINEAR_HH

#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <utility>
#include <vector>

namespace gcs
{
    /**
     * \brief An integer variable with a coefficient for multiplication.
     *
     * \ingroup Core
     */
    using CoefficientAndVariable = std::pair<Integer, IntegerVariableID>;

    /**
     * \brief A linear expression, consisting of the sum of variables multiplied
     * by coefficients.
     *
     * \ingroup Core
     */
    using Linear = std::vector<CoefficientAndVariable>;
}

#endif
