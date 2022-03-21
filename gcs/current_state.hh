/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CURRENT_STATE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CURRENT_STATE_HH

#include <gcs/innards/state-fwd.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <exception>
#include <functional>
#include <memory>
#include <optional>

namespace gcs
{
    /**
     * \brief Thrown by CurrentState::operator() if a variable does not actually
     * have a unique value.
     *
     * If you are seeing this exception being thrown, it is most likely because
     * you are defining a set of branch variables that do not uniquely determine
     * an assignment for some other variables.
     *
     * \ingroup Core
     */
    class VariableDoesNotHaveUniqueValue : public std::exception
    {
    private:
        std::string _wat;

    public:
        explicit VariableDoesNotHaveUniqueValue(const std::string &);

        virtual auto what() const noexcept -> const char * override;
    };

    /**
     * \brief Gives a way of accessing a variable's value from inside a
     * solution. Usually you will just use CurrentState::operator().
     *
     * Normally this is only valid inside a callback, and cannot be stored for
     * later use.  Use CurrentState::clone() if you need to save the state.
     *
     * \ingroup Core
     */
    class CurrentState
    {
    private:
        std::unique_ptr<std::optional<innards::State>> _state_copy;
        innards::State & _full_state;

        explicit CurrentState(std::optional<innards::State> &&);

    public:
        /**
         * \name Constructors, destructors, etc.
         * @{
         */
        explicit CurrentState(innards::State & state);
        ~CurrentState();

        CurrentState(CurrentState &&);

        CurrentState(const CurrentState &) = delete;
        auto operator=(const CurrentState &) -> CurrentState & = delete;
        auto operator=(CurrentState &&) -> CurrentState & = delete;

        [[ nodiscard ]] auto clone() const -> CurrentState;

        ///@}

        /**
         * \name Querying the current state of a variable.
         * @{
         */

        /**
         * \brief Fetch a variable's unique value.
         *
         * This is the only part of this class that most consumers need: returns
         * the value of a particular variable, or throws VariableDoesNotHaveUniqueValue
         * if the variable does not have a single value (for example, if it is not a
         * branch variable and is not uniquely constrained).
         */
        [[nodiscard]] auto operator()(const IntegerVariableID &) const -> Integer;

        /**
         * \brief Does this variable have a unique value?
         */
        [[nodiscard]] auto has_single_value(const IntegerVariableID) const -> bool;

        /**
         * \brief What is the lowest value in this variable's domain?
         */
        [[nodiscard]] auto lower_bound(const IntegerVariableID) const -> Integer;

        /**
         * \brief What is the highest value in this variable's domain?
         */
        [[nodiscard]] auto upper_bound(const IntegerVariableID) const -> Integer;

        /**
         * \brief Is this value present in the variable's domain?
         */
        [[nodiscard]] auto in_domain(const IntegerVariableID, Integer) const -> bool;

        /**
         * \brief Calls the supplied function once for each value in the
         * variable's domain.
         */
        auto for_each_value(const IntegerVariableID, std::function<auto(Integer)->void>) const -> void;

        ///@}
    };
}

#endif
