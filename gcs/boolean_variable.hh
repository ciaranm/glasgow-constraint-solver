/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_BOOLEAN_VARIABLE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_BOOLEAN_VARIABLE_HH 1

#include <variant>

namespace gcs
{
    struct BooleanVariableID
    {
        std::variant<unsigned long long, bool> index_or_const_value;

        explicit BooleanVariableID(unsigned long long x) :
            index_or_const_value(x)
        {
        }

        explicit BooleanVariableID(bool x) :
            index_or_const_value(x)
        {
        }
    };

    [[ nodiscard ]] inline auto constant_variable(bool x) -> BooleanVariableID
    {
        return BooleanVariableID(x);
    }
}

#endif
