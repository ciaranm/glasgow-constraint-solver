/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROBLEM_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROBLEM_HH 1

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>
#include <gcs/linear.hh>
#include <gcs/literal.hh>
#include <gcs/proof.hh>
#include <gcs/state.hh>

#include <functional>
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
            explicit Problem(Proof &&);

            ~Problem();

            Problem(const Problem &) = delete;
            Problem & operator= (const Problem &) = delete;

            [[ nodiscard ]] auto create_integer_variable(
                    Integer lower,
                    Integer upper,
                    const std::optional<std::string> & name = std::nullopt,
                    bool need_ge = true) -> IntegerVariableID;

            [[ nodiscard ]] auto create_state() const -> State;
            [[ nodiscard ]] auto propagate(State &) const -> bool;

            [[ nodiscard ]] auto find_branching_variable(State &) const -> std::optional<IntegerVariableID>;

            auto post(Constraint &&) -> void;

            auto branch_on(const std::vector<IntegerVariableID> &) -> void;

            auto optional_proof() const -> std::optional<Proof> &;
    };
}

#endif
