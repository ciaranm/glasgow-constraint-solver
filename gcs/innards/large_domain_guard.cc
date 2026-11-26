#include <gcs/innards/environment.hh>
#include <gcs/innards/large_domain_guard.hh>

#include <algorithm>
#include <cstdlib>
#include <limits>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
using std::format;
#else
#include <fmt/core.h>
using fmt::format;
#endif

using namespace gcs;
using namespace gcs::innards;

LargeDomainGuardTripped::LargeDomainGuardTripped(const char * what_was_too_big, long long how_big, long long limit) :
    UnexpectedException{format("Large domain guard tripped: {} is {}, over the limit of {}. This build was configured with "
                               "-DGCS_LARGE_DOMAIN_GUARD=ON, which turns work proportional to a domain's width into a "
                               "diagnostic; see dev_docs/large-domains.md and issue #833",
        what_was_too_big, how_big, limit)}
{
}

auto gcs::innards::large_domain_guard_limit() -> long long
{
    // 100000 by default: see the header for why this sits where it does. A
    // malformed override is ignored with a warning, and one past long long is
    // clamped.
    static const long long limit = static_cast<long long>(std::min<unsigned long long>(
        non_negative_count_from_environment("GCS_LARGE_DOMAIN_GUARD_LIMIT", 100000), std::numeric_limits<long long>::max()));
    return limit;
}

auto gcs::innards::throw_large_domain_guard_tripped(const char * what_was_too_big, long long how_big) -> void
{
    throw LargeDomainGuardTripped{what_was_too_big, how_big, large_domain_guard_limit()};
}
