/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CURRENT_STATE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CURRENT_STATE_HH

#include <gcs/innards/state-fwd.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <exception>
#include <functional>

namespace gcs
{
    class VariableDoesNotHaveUniqueValue : public std::exception
    {
    private:
        std::string _wat;

    public:
        explicit VariableDoesNotHaveUniqueValue(const std::string &);

        virtual auto what() const noexcept -> const char * override;
    };

    class CurrentState
    {
    private:
        innards::State & _full_state;

    public:
        explicit CurrentState(innards::State & state);
        ~CurrentState() = default;

        CurrentState(const CurrentState &) = delete;
        CurrentState & operator=(const CurrentState &) = delete;

        // This is the only part of this class that most consumers need: returns
        // the value of a particular variable, or throws VariableDoesNotHaveUniqueValue
        // if the variable does not have a single value (e.g. if it is not a
        // branch variable and is not uniquely constrained).
        [[nodiscard]] auto operator()(const IntegerVariableID &) const -> Integer;

        [[nodiscard]] auto has_single_value(const IntegerVariableID) const -> bool;
        [[nodiscard]] auto lower_bound(const IntegerVariableID) const -> Integer;
        [[nodiscard]] auto upper_bound(const IntegerVariableID) const -> Integer;
        [[nodiscard]] auto in_domain(const IntegerVariableID, Integer) const -> bool;
        auto for_each_value(const IntegerVariableID, std::function<auto(Integer)->void>) const -> void;
    };
}

#endif
