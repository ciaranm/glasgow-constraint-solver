/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_EXCEPTION_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_EXCEPTION_HH 1

#include <exception>
#include <experimental/source_location>
#include <string>

namespace gcs
{
    class UnexpectedException :
        public std::exception
    {
        private:
            std::string _wat;

        public:
            explicit UnexpectedException(const std::string &);

            virtual auto what() const noexcept -> const char * override;
    };

    class NonExhaustiveSwitch :
        public UnexpectedException
    {
        public:
            explicit NonExhaustiveSwitch(const std::experimental::source_location & = std::experimental::source_location::current());
    };

    class UnimplementedException :
        public UnexpectedException
    {
        public:
            explicit UnimplementedException(const std::experimental::source_location & = std::experimental::source_location::current());
    };
}

#endif
