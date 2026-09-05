#include <gcs/innards/large_domain_guard.hh>

#include <cstdlib>
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
    static const long long limit = []() -> long long {
        if (const char * e = std::getenv("GCS_LARGE_DOMAIN_GUARD_LIMIT"))
            return std::strtoll(e, nullptr, 10);
        return 100000; // see the header for why this sits where it does
    }();
    return limit;
}

auto gcs::innards::throw_large_domain_guard_tripped(const char * what_was_too_big, long long how_big) -> void
{
    throw LargeDomainGuardTripped{what_was_too_big, how_big, large_domain_guard_limit()};
}
