/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_LITERAL_UTILS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_LITERAL_UTILS_HH

#include <gcs/literal.hh>

#include <optional>
#include <utility>
#include <vector>

namespace gcs::innards
{
    [[nodiscard]] auto is_literally_true_or_false(const Literal &) -> std::optional<bool>;

    [[nodiscard]] auto is_literally_true(const Literal &) -> bool;

    [[nodiscard]] auto is_literally_false(const Literal &) -> bool;

    [[nodiscard]] auto debug_string(const Literal &) -> std::string;
}

#endif
