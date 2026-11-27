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
     * \brief What a threshold override comes to: the count to use, and whether
     * the value was set but not valid, which the caller reports.
     *
     * \ingroup Innards
     */
    struct CountSetting
    {
        unsigned long long value;
        bool malformed;
    };

    /**
     * \brief Decide a threshold override from its raw value, as getenv() gives
     * it: `default_value` when it is unset (null) or empty, as an empty
     * GCS_ASSERTION_LEVEL is; the count when it is valid (see
     * parse_non_negative_count(), so a value past the range of unsigned long
     * long is not); otherwise `default_value`, marked malformed.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto count_setting(const char * value, unsigned long long default_value) -> CountSetting;

    /**
     * \brief Read a threshold override from the environment variable `name`,
     * as count_setting() decides it. A value that is set but not valid is
     * ignored with a warning on stderr, as GCS_ASSERTION_LEVEL's is, rather
     * than read as whatever strtoull makes of it (0 for text, a huge count for
     * a negative number). An empty value counts as unset, with no warning.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto non_negative_count_from_environment(const char * name, unsigned long long default_value) -> unsigned long long;

    /**
     * \brief A count as a long long, for a threshold compared against one: a
     * count past the long long range is clamped to its maximum, which already
     * means "never" or "always" for any threshold that reads it.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto count_as_long_long(unsigned long long count) -> long long;
}

#endif // GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_ENVIRONMENT_HH
