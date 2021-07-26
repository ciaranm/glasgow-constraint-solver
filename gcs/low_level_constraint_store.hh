/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_LOW_LEVEL_CONSTRAINT_STORE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_LOW_LEVEL_CONSTRAINT_STORE_HH 1

#include <gcs/linear.hh>
#include <gcs/literal.hh>
#include <gcs/state.hh>

#include <functional>

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
            [[ nodiscard ]] auto propagate_propagators(State &) const -> Inference;

        public:
            LowLevelConstraintStore();
            ~LowLevelConstraintStore();

            LowLevelConstraintStore(const LowLevelConstraintStore &) = delete;
            LowLevelConstraintStore & operator= (const LowLevelConstraintStore &) = delete;

            auto cnf(Literals && lits) -> void;
            auto lin_le(Linear && coeff_vars, Integer value) -> void;
            auto propagator(PropagationFunction &&) -> void;

            [[ nodiscard ]] auto propagate(State &) const -> bool;
    };
}

#endif
