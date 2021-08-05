/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_TABLE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_TABLE_HH 1

#include <gcs/variable_id.hh>
#include <gcs/integer.hh>

#include <vector>

namespace gcs
{
    struct Table
    {
        IntegerVariableID selector;
        std::vector<IntegerVariableID> vars;
        std::vector<std::vector<Integer> > tuples;
    };
}

#endif
