/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_DETAIL_VARIABLE_ID_UTILS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_DETAIL_VARIABLE_ID_UTILS_HH 1

#include <gcs/variable_id.hh>

#include <string>
#include <utility>

namespace gcs
{
    [[nodiscard]] auto underlying_direct_variable_and_offset(const IntegerVariableID var) -> std::pair<DirectIntegerVariableID, Integer>;

    [[nodiscard]] auto debug_string(const IntegerVariableID &) -> std::string;

    [[nodiscard]] auto debug_string(const VariableID &) -> std::string;
}

#endif
