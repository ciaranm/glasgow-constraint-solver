/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATE_HH 1

#include <gcs/integer_variable.hh>
#include <gcs/literal.hh>

#include <exception>
#include <functional>
#include <memory>
#include <optional>

namespace gcs
{
    enum class Inference
    {
        NoChange,
        Change,
        Contradiction
    };

    class VariableDoesNotHaveUniqueValue :
        public std::exception
    {
        private:
            std::string _wat;

        public:
            explicit VariableDoesNotHaveUniqueValue(const std::string &);

            virtual auto what() const noexcept -> const char * override;
    };

    struct Timestamp
    {
        unsigned long long when;

        explicit Timestamp(unsigned long long w) :
            when(w)
        {
        }
    };

    class State
    {
        private:
            struct Imp;
            std::unique_ptr<Imp> _imp;

            [[ nodiscard ]] auto infer_boolean(const LiteralFromBooleanVariable & lit) -> Inference;
            [[ nodiscard ]] auto infer_integer(const LiteralFromIntegerVariable & lit) -> Inference;

            [[ nodiscard ]] auto non_constant_integer_variable(const IntegerVariableID) -> IntegerVariable &;
            [[ nodiscard ]] auto integer_variable(const IntegerVariableID, IntegerVariable & space) -> IntegerVariable &;
            [[ nodiscard ]] auto integer_variable(const IntegerVariableID, IntegerVariable & space) const -> const IntegerVariable &;

            auto remember_change(const VariableID) -> void;

        public:
            explicit State();
            State(State &&) noexcept;
            ~State();

            State(const State &) = delete;
            State & operator= (const State &) = delete;

            [[ nodiscard ]] State clone() const;

            auto create_integer_variable(Integer lower, Integer upper) -> IntegerVariableID;

            [[ nodiscard ]] auto infer(const Literal & lit) -> Inference;

            auto guess(const Literal & lit) -> void;

            [[ nodiscard ]] auto lower_bound(const IntegerVariableID) const -> Integer;
            [[ nodiscard ]] auto upper_bound(const IntegerVariableID) const -> Integer;
            [[ nodiscard ]] auto in_domain(const IntegerVariableID, Integer) const -> bool;
            [[ nodiscard ]] auto optional_single_value(const IntegerVariableID) const -> std::optional<Integer>;
            [[ nodiscard ]] auto domain_size(const IntegerVariableID) const -> Integer;
            auto for_each_value(const IntegerVariableID, std::function<auto (Integer) -> void>) const -> void;

            [[ nodiscard ]] auto optional_single_value(const BooleanVariableID) const -> std::optional<bool>;

            [[ nodiscard ]] auto operator() (const IntegerVariableID &) const -> Integer;
            [[ nodiscard ]] auto operator() (const BooleanVariableID &) const -> bool;

            [[ nodiscard ]] auto new_epoch() -> Timestamp;
            auto backtrack(Timestamp) -> void;
    };
}

#endif
