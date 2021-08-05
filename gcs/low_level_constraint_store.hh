/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_LOW_LEVEL_CONSTRAINT_STORE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_LOW_LEVEL_CONSTRAINT_STORE_HH 1

#include <gcs/linear.hh>
#include <gcs/literal.hh>
#include <gcs/problem.hh>
#include <gcs/state.hh>
#include <gcs/table.hh>

#include <functional>
#include <vector>

namespace gcs
{
    using PropagationFunction = std::function<auto (State &) -> Inference>;

    class LowLevelConstraintStore
    {
        private:
            struct Imp;
            std::unique_ptr<Imp> _imp;

            [[ nodiscard ]] auto propagate_cnfs(State &) const -> Inference;
            [[ nodiscard ]] auto propagate_lin_les(State &) const -> Inference;
            [[ nodiscard ]] auto propagate_table(const Table &, State &) const -> Inference;

        public:
            explicit LowLevelConstraintStore(Problem * const);
            ~LowLevelConstraintStore();

            LowLevelConstraintStore(const LowLevelConstraintStore &) = delete;
            LowLevelConstraintStore & operator= (const LowLevelConstraintStore &) = delete;

            auto cnf(Literals && lits) -> void;
            auto lin_le(Linear && coeff_vars, Integer value) -> void;
            auto propagator(PropagationFunction &&, const std::vector<VariableID> & trigger_vars) -> void;
            auto table(std::vector<IntegerVariableID> &&, std::vector<std::vector<Integer> > &&) -> void;

            [[ nodiscard ]] auto create_auxilliary_integer_variable(Integer, Integer) -> IntegerVariableID;

            [[ nodiscard ]] auto propagate(State &) const -> bool;
    };
}

#endif
