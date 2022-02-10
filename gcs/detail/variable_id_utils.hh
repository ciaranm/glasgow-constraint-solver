/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_DETAIL_VARIABLE_ID_UTILS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_DETAIL_VARIABLE_ID_UTILS_HH

#include <gcs/variable_id.hh>

#include <concepts>
#include <string>
#include <utility>

namespace gcs
{
    template <typename T_>
    concept IntegerVariableIDLike = std::is_convertible_v<T_, IntegerVariableID>;

    // The following is badly named... Maybe a good name will become evident once the variants
    // gain more items?
    using DirectIntegerVariableID = std::variant<SimpleIntegerVariableID, ConstantIntegerVariableID>;

    [[nodiscard]] auto underlying_direct_variable_and_offset(const IntegerVariableID & var) -> std::pair<DirectIntegerVariableID, Integer>;

    [[nodiscard]] auto underlying_direct_variable_and_offset(const SimpleIntegerVariableID & var) -> std::pair<SimpleIntegerVariableID, Integer>;
    [[nodiscard]] auto underlying_direct_variable_and_offset(const ConstantIntegerVariableID & var) -> std::pair<ConstantIntegerVariableID, Integer>;
    [[nodiscard]] auto underlying_direct_variable_and_offset(const ViewOfIntegerVariableID & var) -> std::pair<SimpleIntegerVariableID, Integer>;

    [[nodiscard]] auto debug_string(const IntegerVariableID &) -> std::string;

    [[nodiscard]] auto debug_string(const VariableID &) -> std::string;
}

#endif
