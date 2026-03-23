#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATS_HH

#include <algorithm>
#include <chrono>
#include <format>
#include <iosfwd>
#include <sstream>
#include <string>
#include <tuple>
#include <vector>

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

template <>
struct std::formatter<gcs::Stats>
{
    constexpr auto parse(std::format_parse_context & ctx)
    {
        return ctx.begin();
    }

    auto format(const gcs::Stats & stats, std::format_context & ctx) const
    {
        std::stringstream s;
        s << stats;
        return std::format_to(ctx.out(), "{}", s.str());
    }
};

#endif
