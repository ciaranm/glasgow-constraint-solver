/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_BOOLEAN_VARIABLE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_BOOLEAN_VARIABLE_HH 1

namespace gcs
{
    struct BooleanVariableID
    {
        unsigned long long index;

        explicit BooleanVariableID(unsigned long long x) :
            index(x)
        {
        }
    };
}

#endif
