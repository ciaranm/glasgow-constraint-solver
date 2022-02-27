/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_EXCEPTION_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_EXCEPTION_HH

#include <exception>
#include <string>
#include <version>

#if __has_include(<source_location>) && __cpp_lib_source_location
#  include <source_location>
#endif

namespace gcs
{
    class UnexpectedException : public std::exception
    {
    private:
        std::string _wat;

    public:
        explicit UnexpectedException(const std::string &);

        virtual auto what() const noexcept -> const char * override;
    };

    class NonExhaustiveSwitch : public UnexpectedException
    {
    public:
#if __has_include(<source_location>) && __cpp_lib_source_location
        explicit NonExhaustiveSwitch(const std::source_location & = std::source_location::current());
#else
        explicit NonExhaustiveSwitch();
#endif
    };

    class UnimplementedException : public UnexpectedException
    {
    public:
#if __has_include(<source_location>) && __cpp_lib_source_location
        explicit UnimplementedException(const std::source_location & = std::source_location::current());
#else
        explicit UnimplementedException();
#endif
    };
}

#endif
