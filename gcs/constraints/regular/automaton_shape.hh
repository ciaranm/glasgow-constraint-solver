#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_REGULAR_AUTOMATON_SHAPE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_REGULAR_AUTOMATON_SHAPE_HH

#include <gcs/exception.hh>

#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief The checks every automaton constructor of the Regular family makes
     * on the indices it is given, so that a bad one is refused at construction
     * rather than read past the end of a vector later (#1333).
     *
     * States are numbered `0 .. num_states - 1`, with 0 the start, so there has
     * to be at least one. There may be at most one transition row per state; a
     * shorter table means the missing states have no transitions, which the
     * constructor pads. Every final state has to be a state.
     *
     * \ingroup Innards
     */
    inline auto check_automaton_states(std::string_view who, long num_states, std::size_t rows, const std::vector<long> & final_states) -> void
    {
        if (num_states < 1)
            throw InvalidProblemDefinitionException{
                std::string{who} + ": num_states must be at least 1, since state 0 is the start, not " + std::to_string(num_states)};
        if (rows > static_cast<std::size_t>(num_states))
            throw InvalidProblemDefinitionException{std::string{who} + ": " + std::to_string(rows) + " transition rows for " +
                std::to_string(num_states) + " states; there may be at most one row per state"};
        for (auto f : final_states)
            if (f < 0 || f >= num_states)
                throw InvalidProblemDefinitionException{
                    std::string{who} + ": final state " + std::to_string(f) + " is not a state in 0.." + std::to_string(num_states - 1)};
    }

    /**
     * \brief Check one transition's target. In the single-target forms, `-1`
     * means "no transition", as a missing entry does; the set-valued form has
     * no such sentinel, since an absent or empty set already says it.
     *
     * \ingroup Innards
     */
    inline auto check_automaton_target(std::string_view who, long num_states, std::size_t from, long target, bool minus_one_is_none) -> void
    {
        if (minus_one_is_none && target == -1)
            return;
        if (target < 0 || target >= num_states)
            throw InvalidProblemDefinitionException{std::string{who} + ": state " + std::to_string(from) + " has a transition to " +
                std::to_string(target) + ", which is not a state in 0.." + std::to_string(num_states - 1)};
    }
}

#endif
