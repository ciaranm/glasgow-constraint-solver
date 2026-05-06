#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_INTEGER_OVERFLOW_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_INTEGER_OVERFLOW_HH

#include <gcs/exception.hh>

namespace gcs::innards
{
    /**
     * \brief Thrown when an Integer arithmetic operation would overflow,
     * divide by zero, or otherwise produce an undefined result.
     */
    class IntegerOverflow : public UnexpectedException
    {
    public:
        IntegerOverflow(const char * op, long long a, long long b);
        IntegerOverflow(const char * op, long long a);
    };

    [[noreturn]] auto throw_integer_overflow(const char * op, long long a, long long b) -> void;
    [[noreturn]] auto throw_integer_overflow(const char * op, long long a) -> void;
}

#endif
