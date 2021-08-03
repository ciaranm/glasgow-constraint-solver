/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROBLEM_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROBLEM_HH 1

#include <gcs/constraint.hh>
#include <gcs/integer_variable.hh>
#include <gcs/linear.hh>
#include <gcs/literal.hh>
#include <gcs/state.hh>

#include <memory>
#include <optional>
#include <vector>

namespace gcs
{
    class Problem
    {
        private:
            struct Imp;
            std::unique_ptr<Imp> _imp;

        public:
            Problem();
            ~Problem();

            Problem(const Problem &) = delete;
            Problem & operator= (const Problem &) = delete;

            auto create_integer_variable(Integer lower, Integer upper) -> IntegerVariableID;

            [[ nodiscard ]] auto create_state() const -> State;
            [[ nodiscard ]] auto propagate(State &) const -> bool;

            [[ nodiscard ]] auto find_branching_variable(State &) const -> std::optional<IntegerVariableID>;

            auto post(Constraint &&) -> void;

            auto branch_on(const std::vector<IntegerVariableID> &) -> void;
    };
}

#endif
