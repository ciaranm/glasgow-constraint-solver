/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROBLEM_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROBLEM_HH 1

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

            [[ nodiscard ]] auto propagate_cnfs(State &) const -> Inference;
            [[ nodiscard ]] auto propagate_lin_les(State &) const -> Inference;

        public:
            Problem();
            ~Problem();

            Problem(const Problem &) = delete;
            Problem & operator= (const Problem &) = delete;

            auto allocate_integer_variable(Integer lower, Integer upper) -> IntegerVariableID;

            auto cnf(Literals && lits) -> void;

            auto lin_le(Linear && coeff_vars, Integer value) -> void;
            auto lin_eq(Linear && coeff_vars, Integer value) -> void;

            auto all_different(const std::vector<IntegerVariableID> & vars) -> void;

            auto element(IntegerVariableID var, IntegerVariableID idx_var, const std::vector<IntegerVariableID> & vars) -> void;

            [[ nodiscard ]] auto create_initial_state() const -> State;
            [[ nodiscard ]] auto propagate(State &) const -> bool;

            [[ nodiscard ]] auto find_branching_variable(State &) const -> std::optional<IntegerVariableID>;
    };
}

#endif
