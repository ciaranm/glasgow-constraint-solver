#include <gcs/exception.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
using std::format;
#else
#include <fmt/core.h>
using fmt::format;
#endif

using namespace gcs;

#if __has_include(<source_location>) && __cpp_lib_source_location
using std::source_location;
#endif
using std::string;

UnexpectedException::UnexpectedException(const string & w) :
    _wat("unexpected problem: " + w)
{
}

auto UnexpectedException::what() const noexcept -> const char *
{
    return _wat.c_str();
}

InvalidProblemDefinitionException::InvalidProblemDefinitionException(const string & w) :
    _wat("invalid problem definition: " + w)
{
}

auto InvalidProblemDefinitionException::what() const noexcept -> const char *
{
    return _wat.c_str();
}

#if __has_include(<source_location>) && __cpp_lib_source_location

namespace
{
    auto where_does_it_hurt(const source_location & where) -> string
    {
        return format("{}:{} in {}", where.file_name(), where.line(), where.function_name());
    }
}

UnimplementedException::UnimplementedException(const source_location & where) :
    UnexpectedException{"unimplemented at " + where_does_it_hurt(where)}
{
}

UnimplementedException::UnimplementedException(const string & msg, const source_location & where) :
    UnexpectedException{"unimplemented: " + msg + " at " + where_does_it_hurt(where)}
{
}

NonExhaustiveSwitch::NonExhaustiveSwitch(const source_location & where) :
    UnexpectedException{"non-exhaustive at " + where_does_it_hurt(where)}
{
}

#else

UnimplementedException::UnimplementedException() :
    UnexpectedException{"unimplemented, source location not supported by your compiler"}
{
}

UnimplementedException::UnimplementedException(const string & msg) :
    UnexpectedException{"unimplemented " + msg + ", source location not supported by your compiler"}
{
}

NonExhaustiveSwitch::NonExhaustiveSwitch() :
    UnexpectedException{"unimplemented, source location not supported by your compiler"}
{
}

#endif
