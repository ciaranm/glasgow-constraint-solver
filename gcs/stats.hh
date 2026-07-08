#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATS_HH

#include <chrono>
#include <iosfwd>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#else
#include <fmt/ostream.h>
#endif

namespace gcs
{
    /**
     * \brief Statistics from solving.
     *
     * \sa gcs::solve()
     * \sa gcs::solve_with()
     * \ingroup Core
     */
    struct Stats final
    {
        unsigned long long recursions = 0;
        unsigned long long failures = 0;
        unsigned long long propagations = 0;
        unsigned long long effectful_propagations = 0;
        unsigned long long contradicting_propagations = 0;
        unsigned long long solutions = 0;
        unsigned long long max_depth = 0;

        unsigned long long n_propagators = 0;

        /// How many propagators had their EnableButIdempotent claims ignored
        /// because their trigger scope aliases a variable (directly or
        /// through a view). A downgraded propagator just keeps today's
        /// always-requeue behaviour; this counter makes the downgrade
        /// observable.
        unsigned long long idempotence_downgrades = 0;

        std::chrono::microseconds solve_time;
    };

    /**
     * \brief Stats can be written to an ostream, for convenience.
     *
     * \sa Stats
     * \ingroup Core
     */
    auto operator<<(std::ostream &, const Stats &) -> std::ostream &;
}

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
template <>
struct std::formatter<gcs::Stats> : std::formatter<std::string>
{
    auto format(const gcs::Stats & s, std::format_context & ctx) const
    {
        std::ostringstream oss;
        oss << s;
        return std::formatter<std::string>::format(oss.str(), ctx);
    }
};
#else
template <>
struct fmt::formatter<gcs::Stats> : ostream_formatter
{
};
#endif

#endif
