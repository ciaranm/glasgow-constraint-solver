/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROPAGATORS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROPAGATORS_HH

#include <gcs/extensional.hh>
#include <gcs/innards/linear_utils.hh>
#include <gcs/innards/literal_utils.hh>
#include <gcs/innards/proof.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/innards/state.hh>
#include <gcs/linear.hh>
#include <gcs/literal.hh>
#include <gcs/problem.hh>

#include <atomic>
#include <functional>
#include <utility>
#include <vector>

namespace gcs::innards
{
    using PropagationFunction = std::function<auto(State &)->std::pair<Inference, PropagatorState>>;

    /**
     * \brief Tell Propagators when a Constraint's propagators should be triggered.
     *
     * Every propagator will be called at least once, when search starts.
     * Propagators must assume they may be called at any time, even if their
     * events have not triggered.
     *
     * Only the strongest condition needs to be registered: if a variable is
     * instantiated, then bounds and change events will also trigger, and if a
     * variable's bounds change then change events will trigger.
     *
     * \ingroup Innards
     * \sa Propagators::install
     */
    struct Triggers
    {
        std::vector<IntegerVariableID> on_change = {};
        std::vector<IntegerVariableID> on_bounds = {};
        std::vector<IntegerVariableID> on_instantiated = {};
    };

    /**
     * \brief Every Constraint creates one or more propagation functions, which
     * are given to a Propagators instance to manage.
     *
     * \ingroup Innards
     */
    class Propagators
    {
    private:
        struct Imp;
        std::unique_ptr<Imp> _imp;

        auto trigger_on_change(IntegerVariableID, int id) -> void;
        auto trigger_on_bounds(IntegerVariableID, int id) -> void;
        auto trigger_on_instantiated(IntegerVariableID, int id) -> void;
        auto increase_degree(IntegerVariableID) -> void;

    public:
        /**
         * \name Constructors, destructors, etc.
         */
        ///@{
        explicit Propagators(Problem * const);
        ~Propagators();

        Propagators(const Propagators &) = delete;
        auto operator=(const Propagators &) -> Propagators & = delete;
        ///@}

        /**
         * \name One-off operations for things that follow immediately from a Constraint's definition.
         */
        ///@{

        /**
         * Can be called by a Constraint if it is contradictory by definition.
         */
        auto model_contradiction(const State &, const std::string & explain_yourself) -> void;

        /**
         * Called by a Constraint if a variable's lower bound must, by definition, be at least a value.
         */
        auto trim_lower_bound(const State &, IntegerVariableID var, Integer val, const std::string & explain_yourself) -> void;

        /**
         * Called by a Constraint if a variable's upper bound must, by definition, be at least a value.
         */
        auto trim_upper_bound(const State &, IntegerVariableID var, Integer val, const std::string & explain_yourself) -> void;

        ///@}

        /**
         * \name Definitions, for proofs.
         */
        ///@{

        /**
         * Are definitions actually wanted?
         */
        [[nodiscard]] auto want_definitions() const -> bool;

        /**
         * Add a CNF definition to a Proof model.
         */
        auto define_cnf(const State &, Literals && lits) -> std::optional<ProofLine>;

        /**
         * Add an at-most-one constraint to a Proof model.
         */
        auto define_at_most_one(const State &, Literals && lits) -> std::optional<ProofLine>;

        /**
         * Add a pseudo-Boolean greater-or-equal constraint to a Proof model.
         */
        auto define_pseudoboolean_ge(const State &, WeightedPseudoBooleanTerms && lits, Integer) -> std::optional<ProofLine>;

        /**
         * Add a linear less-or-equal constraint to a Proof model.
         */
        auto define_linear_le(const State &, const Linear &, Integer value,
            std::optional<ReificationTerm> half_reif) -> std::optional<ProofLine>;

        /**
         * Add linear equality constraint to a Proof model.
         */
        auto define_linear_eq(const State &, const Linear &, Integer value,
            std::optional<ReificationTerm> half_reif) -> std::optional<ProofLine>;

        ///@}

        /**
         * \name Turning a Constraint into propagators
         */
        ///@{

        /**
         * Install the specified propagation function, which will be called
         * when triggered. All constraints are called at least once when search
         * starts, even if no Triggers are specified, and a constraint may be
         * called even if its trigger condition is not met.
         */
        auto install(const State &, PropagationFunction &&, const Triggers & trigger_vars, const std::string & name) -> void;

        /**
         * Install a propagator for the provided table constraint, and take
         * care of definitions if want_definitions() is true. This is used by
         * Table, but also by various other constraints that turn themselves
         * into table-like constraints.
         *
         * \sa gcs::innards::propagate_extensional()
         */
        auto define_and_install_table(const State &, std::vector<IntegerVariableID> &&,
            ExtensionalTuples &&, const std::string & name) -> void;

        ///@}

        /**
         * \name Support variables.
         */
        ///@{

        /**
         * Create an IntegerVariableID that is associated with a constraint,
         * for example for tracking internal state.
         */
        [[nodiscard]] auto create_auxilliary_integer_variable(Integer, Integer, const std::string & name) -> IntegerVariableID;

        /**
         * Create a ProofFlag, that is used only in definitions.
         */
        [[nodiscard]] auto create_proof_flag(const std::string &) -> ProofFlag;

        ///@}

        /**
         * \name Propagation
         */
        ///@{

        /**
         * Propagate every constraint, until either a fixed point or a contradiction is reached.
         */
        [[nodiscard]] auto propagate(State &, const std::optional<IntegerVariableID> & objective_variable,
            const std::optional<Integer> & objective_value, std::atomic<bool> * optional_abort_flag = nullptr) const -> bool;

        ///@}

        /**
         * \name Statistics
         */
        ///@{

        /**
         * Populate propagation statistics.
         *
         * \sa Stats
         */
        auto fill_in_constraint_stats(Stats &) const -> void;

        ///@}

        /**
         * \name Information about constraints
         */
        ///@{

        /**
         * How many constraints is this variable involved in?
         */
        auto degree_of(IntegerVariableID) const -> long;

        ///@}
    };
}

#endif
