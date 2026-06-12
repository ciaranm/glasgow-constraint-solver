#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_EXCEPTION_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_EXCEPTION_HH

#include <exception>
#include <string>
#include <version>

#if __has_include(<source_location>) && __cpp_lib_source_location
#include <source_location>
#endif

namespace gcs
{
    /**
     * \brief Base class for every exception this library throws, holding the
     * message returned by what().
     *
     * Cannot be thrown directly: catch one of the concrete types where
     * possible, or this to handle any solver-related failure uniformly.
     *
     * \sa UnexpectedException
     * \sa InvalidProblemDefinitionException
     * \sa NamingError
     * \sa VariableDoesNotHaveUniqueValue
     * \sa ScpReadError
     * \sa innards::ProofError
     *
     * \ingroup Core
     */
    class MessageException : public std::exception
    {
    private:
        std::string _wat;

    protected:
        explicit MessageException(std::string);

    public:
        [[nodiscard]] virtual auto what() const noexcept -> const char * override;
    };

    /**
     * \brief Thrown if something has gone wrong. This usually indicates a bug
     * in the solver.
     *
     * \ingroup Core
     */
    class UnexpectedException : public MessageException
    {
    public:
        explicit UnexpectedException(const std::string &);
    };

    /**
     * \brief Thrown when a problem definition is semantically invalid: a
     * constraint constructor given mismatched array sizes or negative
     * durations, a variable created with lower bound greater than upper bound,
     * etc. This indicates a bug in the caller, not the solver.
     *
     * \ingroup Core
     */
    class InvalidProblemDefinitionException : public MessageException
    {
    public:
        explicit InvalidProblemDefinitionException(const std::string &);
    };

    /**
     * \brief Thrown if a switch statement is missing a case entry. This usually
     * indicates a bug in the solver.
     *
     * \ingroup Core
     */
    class NonExhaustiveSwitch : public UnexpectedException
    {
    public:
#if __has_include(<source_location>) && __cpp_lib_source_location
        explicit NonExhaustiveSwitch(const std::source_location & = std::source_location::current());
#else
        explicit NonExhaustiveSwitch();
#endif
    };

    /**
     * \brief Thrown if requested functionality is not yet implemented.
     *
     * \ingroup Core
     */
    class UnimplementedException : public UnexpectedException
    {
    public:
#if __has_include(<source_location>) && __cpp_lib_source_location
        explicit UnimplementedException(const std::string & msg, const std::source_location & = std::source_location::current());
        explicit UnimplementedException(const std::source_location & = std::source_location::current());
#else
        explicit UnimplementedException(const std::string & msg);
        explicit UnimplementedException();
#endif
    };
}

#endif
