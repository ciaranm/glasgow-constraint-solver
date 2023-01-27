#include <gcs/exception.hh>

using namespace gcs;

#if __has_include(<source_location>) && __cpp_lib_source_location
using std::source_location;
#endif
using std::string;
#if __has_include(<source_location>) && __cpp_lib_source_location
using std::to_string;
#endif

UnexpectedException::UnexpectedException(const string & w) :
    _wat("unexpected problem: " + w)
{
}

auto UnexpectedException::what() const noexcept -> const char *
{
    return _wat.c_str();
}

#if __has_include(<source_location>) && __cpp_lib_source_location

namespace
{
    auto where_does_it_hurt(const source_location & where) -> string
    {
        return string{where.file_name()} + ":" + to_string(where.line()) + " in " + string{where.function_name()};
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
