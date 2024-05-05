#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROPAGATORS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROPAGATORS_HH

#include <gcs/expression.hh>
#include <gcs/extensional.hh>
#include <gcs/innards/inference_tracker-fwd.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/innards/state.hh>
#include <gcs/problem.hh>

#include <atomic>
#include <functional>
#include <memory>
#include <utility>
#include <vector>

namespace gcs::innards
{
    template <typename StateType_, typename ReturnType_>
    struct ConstraintFunctionHolderBase
    {
        virtual auto operator()(StateType_, InferenceTracker &, ProofLogger * const) -> ReturnType_ = 0;
    };

    template <typename Func_, typename StateType_, typename ReturnType_>
    struct ConstraintFunctionHolder : ConstraintFunctionHolderBase<StateType_, ReturnType_>
    {
        Func_ func;

        explicit ConstraintFunctionHolder(Func_ && f) :
            func(std::move(f))
        {
        }

        auto operator()(StateType_ state, InferenceTracker & inference, ProofLogger * const logger) -> ReturnType_ override
        {
            return func(state, inference, logger);
        }
    };

    template <typename StateType_, typename ReturnType_>
    struct ConstraintFunction
    {
        std::unique_ptr<ConstraintFunctionHolderBase<StateType_, ReturnType_>> func;

        auto operator()(StateType_ state, InferenceTracker & inference, ProofLogger * const logger) -> ReturnType_
        {
            return (*func)(state, inference, logger);
        }

        template <typename Func_>
        explicit(false) ConstraintFunction(Func_ && f) :
            func(new ConstraintFunctionHolder<Func_, StateType_, ReturnType_>{std::move(f)})
        {
        }

        ~ConstraintFunction() = default;

        ConstraintFunction(const ConstraintFunction &) = delete;
        auto operator=(ConstraintFunction &) -> ConstraintFunction & = delete;

        ConstraintFunction(ConstraintFunction &&) = default;
        auto operator=(ConstraintFunction &&) -> ConstraintFunction & = default;
    };

    using PropagationFunction = ConstraintFunction<const State &, PropagatorState>;

    using InitialisationFunction = ConstraintFunction<State &, void>;

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
        explicit Propagators();
        ~Propagators();

        Propagators(const Propagators &) = delete;
        auto operator=(const Propagators &) -> Propagators & = delete;

        Propagators(Propagators &&);
        auto operator=(Propagators &&) -> Propagators &;

        ///@}

        /**
         * \name One-off operations for things that follow immediately from a Constraint's definition.
         */
        ///@{

        /**
         * Can be called by a Constraint if it is contradictory by definition.
         */
        auto model_contradiction(const State &, innards::ProofModel * const, const std::string & explain_yourself) -> void;

        /**
         * Called by a Constraint if a variable's lower bound must, by definition, be at least a value.
         */
        auto trim_lower_bound(const State &, innards::ProofModel * const, IntegerVariableID var, Integer val, const std::string & explain_yourself) -> void;

        /**
         * Called by a Constraint if a variable's upper bound must, by definition, be at least a value.
         */
        auto trim_upper_bound(const State &, innards::ProofModel * const, IntegerVariableID var, Integer val, const std::string & explain_yourself) -> void;

        ///@}

        /**
         * \name Turning a Constraint into propagators
         */
        ///@{

        /**
         * Install the specified propagation function, which makes use of
         * InferenceTracker to handle tracking inference levels. All
         * constraints are called at least once when search starts, even if no
         * Triggers are specified, and a constraint may be called even if its
         * trigger condition is not met.
         */
        auto install(PropagationFunction &&, const Triggers & trigger_vars, const std::string & name) -> void;

        /**
         * Install an initialiser, which will be called once just before search
         * starts.
         */
        auto install_initialiser(InitialisationFunction &&) -> void;

        /**
         * Install a propagator for the provided table constraint, and take
         * care of definitions if want_definitions() is true. This is used by
         * Table, but also by various other constraints that turn themselves
         * into table-like constraints.
         *
         * \sa gcs::innards::propagate_extensional()
         */
        auto define_and_install_table(State &, innards::ProofModel * const, const std::vector<IntegerVariableID> &,
            ExtensionalTuples, const std::string & name) -> void;

        ///@}

        /**
         * \name Support variables.
         */
        ///@{

        /**
         * Create an IntegerVariableID that is associated with a constraint,
         * for example for tracking internal state.
         */
        [[nodiscard]] auto create_auxilliary_integer_variable(State &, Integer, Integer, const std::string & name,
            const IntegerVariableProofRepresentation enc) -> IntegerVariableID;

        ///@}

        /**
         * \name Propagation
         */
        ///@{

        /**
         * Propagate every constraint, until either a fixed point or a contradiction is reached.
         */
        [[nodiscard]] auto propagate(State &, ProofLogger * const,
            const std::optional<std::pair<Literal, HowChanged>> & start_from_guess_rather_than_all_propagators,
            std::atomic<bool> * optional_abort_flag = nullptr) const -> bool;

        /**
         * Call every initialiser, or until a contradiction is reached.
         */
        [[nodiscard]] auto initialise(State &, ProofLogger * const) const -> bool;

        /**
         * Reset to do a root propagation.
         */
        auto requeue_all_propagators() -> void;

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
