/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROBLEM_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROBLEM_HH 1

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>
#include <gcs/literal.hh>
#include <gcs/proof.hh>
#include <gcs/state.hh>
#include <gcs/stats.hh>

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
                    const std::optional<std::string> & name = std::nullopt) -> SimpleIntegerVariableID;

            [[ nodiscard ]] auto create_state() const -> State;
            [[ nodiscard ]] auto propagate(State &) const -> bool;

            [[ nodiscard ]] auto find_branching_variable(State &) const -> std::optional<IntegerVariableID>;

            auto post(Constraint &&) -> void;

            auto branch_on(const std::vector<IntegerVariableID> &) -> void;

            auto minimise(IntegerVariableID) -> void;
            auto update_objective(const State &) -> void;

            auto optional_proof() const -> std::optional<Proof> &;

            auto fill_in_constraint_stats(Stats &) const -> void;
    };
}

#endif
