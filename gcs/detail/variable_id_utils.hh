/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_DETAIL_VARIABLE_ID_UTILS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_DETAIL_VARIABLE_ID_UTILS_HH

#include <gcs/variable_id.hh>

#include <concepts>
#include <string>
#include <utility>

namespace gcs::detail
{
    template <typename T_>
    concept IntegerVariableIDLike = std::is_convertible_v<T_, IntegerVariableID>;

    // The following is badly named... Maybe a good name will become evident once the variants
    // gain more items?
    using DirectIntegerVariableID = std::variant<SimpleIntegerVariableID, ConstantIntegerVariableID>;

    template <typename T_>
    concept DirectIntegerVariableIDLike = std::is_convertible_v<T_, DirectIntegerVariableID>;

    [[nodiscard]] auto debug_string(const IntegerVariableID &) -> std::string;

    [[nodiscard]] auto debug_string(const VariableID &) -> std::string;
}

#endif
