#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINT_ID_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINT_ID_HH

#include <string>
#include <string_view>
#include <type_traits>
#include <variant>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#else
#include <fmt/core.h>
#endif

namespace gcs
{
    struct CurrentlyUnnamedConstraint final
    {
        [[nodiscard]] auto operator<=>(const CurrentlyUnnamedConstraint &) const = default;
        [[nodiscard]] auto as_string() const -> std::string
        {
            return "unnamed";
        }
    };

    struct NumberedConstraint final
    {
        unsigned long long number;
        [[nodiscard]] auto operator<=>(const NumberedConstraint &) const = default;
        [[nodiscard]] auto as_string() const -> std::string
        {
            return "_" + std::to_string(number);
        }
    };

    struct NamedConstraint final
    {
        // A view into a name string owned elsewhere (the Problem's name pool), so
        // that ConstraintID stays trivially copyable -- copying it is a memcpy
        // rather than a std::string copy + the std::variant copy-ctor visit. The
        // viewed string must outlive every copy of this id; the Problem owns it for
        // the whole solve. Compared by content, matching the old std::string field.
        std::string_view name;
        [[nodiscard]] auto operator<=>(const NamedConstraint &) const = default;
        [[nodiscard]] auto as_string() const -> std::string
        {
            return std::string{name};
        }
    };

    // The *identity* of a constraint (`_1`, `_2`, or a caller-given name) -- not
    // its type (`abs`, `all_different`, ...). Kept distinct from "name" because
    // both readings of that word kept getting confused. Trivially copyable (all
    // three alternatives are), so passing or copying one is just a memcpy.
    using ConstraintID = std::variant<CurrentlyUnnamedConstraint, NumberedConstraint, NamedConstraint>;

    // ConstraintID is copied on the hot path -- every reason/hint a propagator builds
    // carries one (see e.g. propagate_non_gac_alldifferent). Keep it trivially copyable
    // so that copy is a memcpy rather than a std::variant copy-ctor visit: in particular
    // do not give any alternative an owning std::string or other non-trivial member.
    static_assert(std::is_trivially_copyable_v<ConstraintID>);

    [[nodiscard]] auto as_string(const ConstraintID &) -> std::string;
}

// The following is needed to allow ConstraintID to be used in format strings.
#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
template <>
struct std::formatter<gcs::ConstraintID> : std::formatter<std::string>
{
    auto format(const gcs::ConstraintID & constraint_id, std::format_context & ctx) const
    {
        return std::formatter<std::string>::format(gcs::as_string(constraint_id), ctx);
    }
};
#else
template <>
struct fmt::formatter<gcs::ConstraintID> : fmt::formatter<std::string>
{
    auto format(const gcs::ConstraintID & constraint_id, fmt::format_context & ctx) const
    {
        return fmt::formatter<std::string>::format(gcs::as_string(constraint_id), ctx);
    }
};
#endif

#endif
