/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATE_HH 1

#include <gcs/integer_variable.hh>
#include <gcs/literal.hh>

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

    class State
    {
        private:
            struct Imp;
            std::unique_ptr<Imp> _imp;

            [[ nodiscard ]] auto infer_boolean(const LiteralFromBooleanVariable & lit) -> Inference;
            [[ nodiscard ]] auto infer_integer(const LiteralFromIntegerVariable & lit) -> Inference;

        public:
            explicit State();
            State(State &&);
            ~State();

            State(const State &) = delete;
            State & operator= (const State &) = delete;

            [[ nodiscard ]] State clone() const;

            auto allocate_integer_variable(Integer lower, Integer upper) -> IntegerVariableID;

            [[ nodiscard ]] auto integer_variable(const IntegerVariableID) -> IntegerVariable &;
            [[ nodiscard ]] auto integer_variable(const IntegerVariableID) const -> const IntegerVariable &;

            [[ nodiscard ]] auto value_of(const IntegerVariableID var) const -> std::optional<Integer>;

            [[ nodiscard ]] auto infer(const Literal & lit) -> Inference;
    };
}

#endif
