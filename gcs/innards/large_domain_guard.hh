#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_LARGE_DOMAIN_GUARD_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_LARGE_DOMAIN_GUARD_HH

#include <gcs/exception.hh>

namespace gcs::innards
{
    /**
     * \brief Thrown when the large-domain guard trips: something iterated over,
     * or allocated an array proportional to, a domain wider than the guard's
     * limit.
     *
     * Only ever thrown in a build configured with `-DGCS_LARGE_DOMAIN_GUARD=ON`,
     * which is a *development* configuration. The guard is a tripwire for finding
     * the work issue #833 is about, not a user-facing safety net: the policy that
     * protects a user is a constraint having somewhere cheap to fall back to, not
     * an exception thrown from the middle of propagation. In a default build the
     * checks compile to nothing at all and this class is never constructed.
     *
     * The message names what was too big and by how much; the audit lane runs one
     * constraint at a time, so the test's name is the attribution for which
     * constraint tripped, and the backtrace (every configuration keeps at least
     * `-g1`) says where.
     *
     * \sa GCS_CHECK_LARGE_DOMAIN
     * \ingroup Innards
     */
    class LargeDomainGuardTripped : public UnexpectedException
    {
    public:
        LargeDomainGuardTripped(const char * what_was_too_big, long long how_big, long long limit);
    };

    /**
     * \brief How wide is too wide, for the large-domain guard.
     *
     * Defaults to 100000, overridable with the `GCS_LARGE_DOMAIN_GUARD_LIMIT`
     * environment variable in the same way as
     * gcs::innards::default_tabulation_threshold(). The default sits in the gap
     * measured on #833 between "free" (10^4) and "costs hundreds of megabytes"
     * (10^6), and well above anything the test suite or a deliberate tabulation
     * asks for.
     *
     * This is emphatically *not* the threshold the large-domain policy itself
     * uses to pick a propagation arm: that one is a separate quantity with its
     * own default, because a guard wants to be far enough above normal work to
     * never fire on it, and a policy wants to be near the cliff.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto large_domain_guard_limit() -> long long;

    [[noreturn]] auto throw_large_domain_guard_tripped(const char * what_was_too_big, long long how_big) -> void;

    /**
     * \brief The guard check itself; prefer the GCS_CHECK_LARGE_DOMAIN macro.
     *
     * \ingroup Innards
     */
    inline auto check_large_domain_guard(const char * what_was_too_big, long long how_big) -> void
    {
        if (how_big > large_domain_guard_limit())
            throw_large_domain_guard_tripped(what_was_too_big, how_big);
    }

    /**
     * \brief Counts values as an iteration hands them out, and trips the guard
     * when one call has been handed too many.
     *
     * Counting the values actually visited is the right measure, and checking
     * the domain's *width* up front is not: a branching heuristic asks for a
     * generator over a billion-value domain and reads one value from it, which
     * is perfectly reasonable work that an up-front width check would condemn.
     * What #833 is about is a loop that walks the whole thing.
     *
     * Compiles to an empty struct with a no-op step() when the guard is off, so
     * an iteration in a default build carries no counter and no branch.
     *
     * \ingroup Innards
     */
    class LargeDomainIterationCounter
    {
#if defined(GCS_LARGE_DOMAIN_GUARD)
    private:
        long long _count = 0;
        const char * _what;

    public:
        explicit LargeDomainIterationCounter(const char * what) : _what(what)
        {
        }

        auto step() -> void
        {
            if (++_count > large_domain_guard_limit())
                throw_large_domain_guard_tripped(_what, _count);
        }
#else
    public:
        explicit LargeDomainIterationCounter(const char *)
        {
        }

        auto step() -> void
        {
        }
#endif
    };
}

/**
 * \brief Trip the large-domain guard if \p n exceeds its limit.
 *
 * For sites that commit to the whole size at once -- an array sized by a
 * domain's span, which is allocated in one go -- where checking up front is
 * exactly right. For an *iteration*, whose caller may stop after one value, use
 * gcs::innards::LargeDomainIterationCounter instead.
 *
 * A macro rather than a function because \p n must not be *evaluated* when the
 * guard is off. With the guard off this expands to nothing, so a default build
 * is unchanged instruction for instruction.
 *
 * \sa gcs::innards::LargeDomainGuardTripped
 * \ingroup Innards
 */
#if defined(GCS_LARGE_DOMAIN_GUARD)
#define GCS_CHECK_LARGE_DOMAIN(what, n) ::gcs::innards::check_large_domain_guard((what), (n))
#else
#define GCS_CHECK_LARGE_DOMAIN(what, n) static_cast<void>(0)
#endif

#endif
