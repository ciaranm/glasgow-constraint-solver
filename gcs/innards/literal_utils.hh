/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_LITERAL_UTILS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_LITERAL_UTILS_HH

#include <gcs/literal.hh>

#include <utility>
#include <vector>

namespace gcs::innards
{
    [[nodiscard]] auto is_literally_true(const Literal &) -> bool;

    [[nodiscard]] auto is_literally_false(const Literal &) -> bool;

    [[nodiscard]] auto debug_string(const Literal &) -> std::string;

    [[nodiscard]] auto sanitise_literals(Literals &) -> bool;

    using WeightedLiterals = std::vector<std::pair<Integer, Literal>>;
}

#endif
