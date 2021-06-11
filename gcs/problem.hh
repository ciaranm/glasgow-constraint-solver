/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROBLEM_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROBLEM_HH 1

#include <gcs/integer_variable.hh>
#include <gcs/literal.hh>
#include <gcs/state.hh>

#include <memory>
#include <optional>
#include <utility>
#include <vector>

namespace gcs
{
    class Problem
    {
        private:
            struct Imp;
            std::unique_ptr<Imp> _imp;

            [[ nodiscard ]] auto propagate_cnfs(State &) const -> bool;
            [[ nodiscard ]] auto propagate_lin_les(State &) const -> bool;

        public:
            Problem();
            ~Problem();

            Problem(const Problem &) = delete;
            Problem & operator= (const Problem &) = delete;

            auto allocate_integer_variable(Integer lower, Integer upper) -> IntegerVariableID;

            auto cnf(std::vector<Literal> && lits) -> void;
            auto all_different(const std::vector<IntegerVariableID> & vars) -> void;
            auto lin_le(std::vector<std::pair<Integer, IntegerVariableID> > & coeff_vars, Integer value) -> void;

            [[ nodiscard ]] auto create_initial_state() const -> State;
            [[ nodiscard ]] auto propagate(State &) const -> bool;

            [[ nodiscard ]] auto find_branching_variable(State &) const -> std::optional<IntegerVariableID>;
    };
}

#endif
