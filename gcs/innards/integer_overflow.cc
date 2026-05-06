#include <gcs/innards/integer_overflow.hh>

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

IntegerOverflow::IntegerOverflow(const char * op, long long a, long long b) :
    UnexpectedException{format("Integer overflow: {} {} {}", a, op, b)}
{
}

IntegerOverflow::IntegerOverflow(const char * op, long long a) :
    UnexpectedException{format("Integer overflow: {}{}", op, a)}
{
}

auto innards::throw_integer_overflow(const char * op, long long a, long long b) -> void
{
    throw IntegerOverflow{op, a, b};
}

auto innards::throw_integer_overflow(const char * op, long long a) -> void
{
    throw IntegerOverflow{op, a};
}
