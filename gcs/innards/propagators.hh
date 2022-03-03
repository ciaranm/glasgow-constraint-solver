/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROPAGATORS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROPAGATORS_HH

#include <gcs/innards/linear_utils.hh>
#include <gcs/innards/literal_utils.hh>
#include <gcs/innards/proof.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/innards/state.hh>
#include <gcs/linear.hh>
#include <gcs/literal.hh>
#include <gcs/problem.hh>

#include <functional>
#include <utility>
#include <vector>

namespace gcs::innards
{
    using PropagationFunction = std::function<auto(State &)->std::pair<Inference, PropagatorState>>;

    struct Triggers
    {
        std::vector<IntegerVariableID> on_change = {};
        std::vector<IntegerVariableID> on_bounds = {};
        std::vector<IntegerVariableID> on_instantiated = {};
    };

    class Propagators
    {
    private:
        struct Imp;
        std::unique_ptr<Imp> _imp;

        auto trigger_on_change(IntegerVariableID, int id) -> void;
        auto trigger_on_bounds(IntegerVariableID, int id) -> void;
        auto trigger_on_instantiated(IntegerVariableID, int id) -> void;

    public:
        explicit Propagators(Problem * const);
        ~Propagators();

        Propagators(const Propagators &) = delete;
        auto operator=(const Propagators &) -> Propagators & = delete;

        auto model_contradiction(const State &, const std::string & explain_yourself) -> void;

        auto trim_lower_bound(const State &, IntegerVariableID var, Integer val, const std::string & explain_yourself) -> void;
        auto trim_upper_bound(const State &, IntegerVariableID var, Integer val, const std::string & explain_yourself) -> void;

        [[nodiscard]] auto want_definitions() const -> bool;

        auto define_cnf(const State &, Literals && lits) -> std::optional<ProofLine>;
        auto define_at_most_one(const State &, Literals && lits) -> std::optional<ProofLine>;
        auto define_pseudoboolean_ge(const State &, WeightedPseudoBooleanTerms && lits, Integer) -> std::optional<ProofLine>;
        auto define_linear_le(const State &, const Linear &, Integer value,
            std::optional<ReificationTerm> half_reif) -> std::optional<ProofLine>;
        auto define_linear_eq(const State &, const Linear &, Integer value,
            std::optional<ReificationTerm> half_reif) -> std::optional<ProofLine>;

        auto install(const State &, PropagationFunction &&, const Triggers & trigger_vars, const std::string & name) -> void;

        auto define_and_install_table(const State &, std::vector<IntegerVariableID> &&,
            std::vector<std::vector<Integer>> &&, const std::string & name) -> void;

        [[nodiscard]] auto create_auxilliary_integer_variable(Integer, Integer, const std::string & name) -> IntegerVariableID;

        [[nodiscard]] auto create_proof_flag(const std::string &) -> ProofFlag;

        [[nodiscard]] auto propagate(State &, const std::optional<IntegerVariableID> & objective_variable,
            const std::optional<Integer> & objective_value) const -> bool;

        auto fill_in_constraint_stats(Stats &) const -> void;
    };
}

#endif
