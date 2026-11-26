#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_ENVIRONMENT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_ENVIRONMENT_HH

#include <optional>
#include <string_view>

namespace gcs::innards
{
    /**
     * \brief Parse a non-negative count, as an environment variable that
     * overrides a threshold gives it: the whole string must be decimal digits
     * whose value fits. Anything else, including a sign, a space or trailing
     * text, gives nullopt.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto parse_non_negative_count(std::string_view value) -> std::optional<unsigned long long>;

    /**
     * \brief Read a threshold override from the environment variable `name`:
     * its value when it is a valid count (see parse_non_negative_count()),
     * otherwise `default_value`. A value that is set but not valid is ignored
     * with a warning on stderr, as GCS_ASSERTION_LEVEL's is, rather than read as
     * whatever strtoull makes of it (0 for text, a huge count for a negative
     * number).
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto non_negative_count_from_environment(const char * name, unsigned long long default_value) -> unsigned long long;
}

#endif // GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_ENVIRONMENT_HH
