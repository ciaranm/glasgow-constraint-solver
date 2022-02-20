/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include <gcs/exception.hh>

using namespace gcs;

using std::source_location;
using std::string;
using std::to_string;

UnexpectedException::UnexpectedException(const string & w) :
    _wat("unexpected problem: " + w)
{
}

auto UnexpectedException::what() const noexcept -> const char *
{
    return _wat.c_str();
}

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

NonExhaustiveSwitch::NonExhaustiveSwitch(const source_location & where) :
    UnexpectedException{"non-exhaustive at " + where_does_it_hurt(where)}
{
}
