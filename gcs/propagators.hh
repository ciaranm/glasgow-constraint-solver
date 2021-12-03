/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROPAGATORS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROPAGATORS_HH 1

#include <gcs/propagators-fwd.hh>
#include <gcs/linear.hh>
#include <gcs/literal.hh>
#include <gcs/problem.hh>
#include <gcs/state.hh>

#include <functional>
#include <utility>
#include <vector>

namespace gcs
{
    using PropagationFunction = std::function<auto (State &) -> std::pair<Inference, PropagatorState> >;

    struct Triggers
    {
        std::vector<VariableID> on_change;
        std::vector<VariableID> on_bounds;
        std::vector<VariableID> on_instantiated;
    };

    class Propagators
    {
        private:
            struct Imp;
            std::unique_ptr<Imp> _imp;

            [[ nodiscard ]] auto propagate_cnfs(State &) const -> Inference;

            auto trigger_on_change(VariableID, int id) -> void;
            auto trigger_on_bounds(VariableID, int id) -> void;
            auto trigger_on_instantiated(VariableID, int id) -> void;

        public:
            explicit Propagators(Problem * const);
            ~Propagators();

            Propagators(const Propagators &) = delete;
            Propagators & operator= (const Propagators &) = delete;

            [[ nodiscard ]] auto want_nonpropagating() const -> bool;

            auto trim_lower_bound(const State &, IntegerVariableID var, Integer val) -> void;
            auto trim_upper_bound(const State &, IntegerVariableID var, Integer val) -> void;

            auto cnf(const State &, Literals && lits, bool propagating) -> std::optional<ProofLine>;
            auto at_most_one(const State &, Literals && lits, bool propagating) -> std::optional<ProofLine>;
            auto pseudoboolean_ge(const State &, WeightedLiterals && lits, Integer, bool propagating) -> std::optional<ProofLine>;
            auto integer_linear_le(const State &, Linear && coeff_vars, Integer value) -> void;
            auto table(const State &, std::vector<IntegerVariableID> &&, std::vector<std::vector<Integer> > &&, const std::string & name) -> void;
            auto propagator(const State &, PropagationFunction &&, const Triggers & trigger_vars, const std::string & name) -> void;

            [[ nodiscard ]] auto create_auxilliary_integer_variable(Integer, Integer, const std::string & name, bool need_ge) -> IntegerVariableID;

            [[ nodiscard ]] auto propagate(State &, const std::optional<IntegerVariableID> & objective_variable,
                    const std::optional<Integer> & objective_value) const -> bool;

            auto fill_in_constraint_stats(Stats &) const -> void;
    };
}

#endif
