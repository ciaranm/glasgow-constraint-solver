#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROPAGATORS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROPAGATORS_HH

#include <gcs/constraint.hh>
#include <gcs/expression.hh>
#include <gcs/extensional.hh>
#include <gcs/innards/inference_tracker-fwd.hh>
#include <gcs/innards/justification.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>
#include <gcs/problem.hh>

#include <atomic>
#include <functional>
#include <memory>
#include <utility>
#include <vector>

namespace gcs::innards
{
    class PropagationFunctionImplBase
    {
    public:
        virtual ~PropagationFunctionImplBase() = default;

        PropagationFunctionImplBase() = default;
        PropagationFunctionImplBase(const PropagationFunctionImplBase &) = delete;
        PropagationFunctionImplBase(PropagationFunctionImplBase &&) = default;

        auto operator=(const PropagationFunctionImplBase &) -> PropagationFunctionImplBase & = delete;
        auto operator=(PropagationFunctionImplBase &&) -> PropagationFunctionImplBase & = default;

        [[nodiscard]] virtual auto operator()(const State & state, SimpleInferenceTracker & tracker, ProofLogger * const logger)
            -> PropagatorState = 0;
        [[nodiscard]] virtual auto operator()(const State & state, EagerProofLoggingInferenceTracker & tracker, ProofLogger * const logger)
            -> PropagatorState = 0;
    };

    template <typename Func_>
    class PropagationFunctionImpl : public PropagationFunctionImplBase
    {
    private:
        Func_ _f;

    public:
        PropagationFunctionImpl(Func_ && f) : _f(std::move(f))
        {
        }

        [[nodiscard]] virtual auto operator()(const State & state, SimpleInferenceTracker & tracker, ProofLogger * const logger)
            -> PropagatorState override
        {
            return _f(state, tracker, logger);
        }

        [[nodiscard]] virtual auto operator()(const State & state, EagerProofLoggingInferenceTracker & tracker, ProofLogger * const logger)
            -> PropagatorState override
        {
            return _f(state, tracker, logger);
        }
    };

    class PropagationFunction
    {
    private:
        std::unique_ptr<PropagationFunctionImplBase> _impl;

    public:
        template <typename Func_>
        PropagationFunction(Func_ && f) : _impl(new PropagationFunctionImpl<Func_>(std::move(f)))
        {
        }

        [[nodiscard]] auto operator()(const State & state, SimpleInferenceTracker & tracker, ProofLogger * const logger) -> PropagatorState
        {
            return _impl->operator()(state, tracker, logger);
        }

        [[nodiscard]] auto operator()(const State & state, EagerProofLoggingInferenceTracker & tracker, ProofLogger * const logger) -> PropagatorState
        {
            return _impl->operator()(state, tracker, logger);
        }
    };

    // Like PropagationFunction, but for initialisers: a type-erased wrapper that
    // can be invoked with either inference tracker, so the proofs-off initialiser
    // pass can use the lean SimpleInferenceTracker too. (A plain std::function
    // would pin the tracker type to one or the other.)
    class InitialisationFunctionImplBase
    {
    public:
        virtual ~InitialisationFunctionImplBase() = default;

        InitialisationFunctionImplBase() = default;
        InitialisationFunctionImplBase(const InitialisationFunctionImplBase &) = delete;
        InitialisationFunctionImplBase(InitialisationFunctionImplBase &&) = default;

        auto operator=(const InitialisationFunctionImplBase &) -> InitialisationFunctionImplBase & = delete;
        auto operator=(InitialisationFunctionImplBase &&) -> InitialisationFunctionImplBase & = default;

        virtual auto operator()(State & state, SimpleInferenceTracker & tracker, ProofLogger * const logger) -> void = 0;
        virtual auto operator()(State & state, EagerProofLoggingInferenceTracker & tracker, ProofLogger * const logger) -> void = 0;
    };

    template <typename Func_>
    class InitialisationFunctionImpl : public InitialisationFunctionImplBase
    {
    private:
        Func_ _f;

    public:
        InitialisationFunctionImpl(Func_ && f) : _f(std::move(f))
        {
        }

        auto operator()(State & state, SimpleInferenceTracker & tracker, ProofLogger * const logger) -> void override
        {
            _f(state, tracker, logger);
        }

        auto operator()(State & state, EagerProofLoggingInferenceTracker & tracker, ProofLogger * const logger) -> void override
        {
            _f(state, tracker, logger);
        }
    };

    class InitialisationFunction
    {
    private:
        std::unique_ptr<InitialisationFunctionImplBase> _impl;

    public:
        template <typename Func_>
        InitialisationFunction(Func_ && f) : _impl(std::make_unique<InitialisationFunctionImpl<Func_>>(std::move(f)))
        {
        }

        auto operator()(State & state, SimpleInferenceTracker & tracker, ProofLogger * const logger) -> void
        {
            _impl->operator()(state, tracker, logger);
        }

        auto operator()(State & state, EagerProofLoggingInferenceTracker & tracker, ProofLogger * const logger) -> void
        {
            _impl->operator()(state, tracker, logger);
        }
    };

    /**
     * \brief Priority for initialisers, controlling the order in which they run.
     *
     * Initialisers run in the order SimpleDefinition, Cheap, Expensive. Within
     * the same priority they run in registration order.
     *
     * \ingroup Innards
     * \sa Propagators::install_initialiser
     */
    enum class InitialiserPriority
    {
        SimpleDefinition,
        Cheap,
        Expensive
    };

    constexpr std::size_t number_of_initialiser_priorities = 3;

    /**
     * \brief Which side of a variable's domain a definitional bound restricts.
     *
     * \ingroup Innards
     * \sa Propagators::define_bound
     */
    enum class Bound
    {
        Lower,
        Upper
    };

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
         * \brief Define a variable's lower or upper bound as part of a Constraint's
         * proof model.
         *
         * Emits an OPB constraint, and installs a SimpleDefinition-priority
         * initialiser that RUPs the bound into the State at search start. If
         * the bound is already implied by the variable's existing domain, no
         * OPB constraint is emitted and no initialiser is installed. If the
         * bound would make the variable's domain empty, the initialiser
         * raises a contradiction at search start — the OPB constraint
         * remains, so the proof reader sees a self-describing reason.
         */
        auto define_bound(const State &, innards::ProofModel * const, IntegerVariableID var, Bound which, Integer val) -> void;

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
         *
         * The ConstraintID identifies which posted constraint this propagator
         * belongs to (the same identity the proof log uses); pass the owning
         * Constraint's constraint_id(). Several propagators may share one
         * ConstraintID. This is recorded so that, for example, a search
         * heuristic can attribute a domain wipeout back to a constraint. It is
         * passed explicitly rather than held as mutable "current constraint"
         * state so it cannot be mis-sequenced.
         */
        auto install(const ConstraintID & constraint_id, PropagationFunction &&, const Triggers & trigger_vars) -> void;

        /**
         * Install an initialiser, which will be called once just before search
         * starts. Initialisers run in priority order
         * (\c SimpleDefinition before \c Cheap before \c Expensive); within
         * the same priority they run in registration order.
         */
        auto install_initialiser(InitialisationFunction &&, InitialiserPriority priority = InitialiserPriority::SimpleDefinition) -> void;

        /**
         * Install an initialiser whose only job is to immediately raise a
         * contradiction with the given Justification (RUP, explicit, or
         * none) and Reason. Convenience wrapper around
         * install_initialiser; intended for cases where the OPB encoding
         * emitted by define_proof_model collapses to a trivially-false
         * constraint and we want propagation to detect that up front.
         *
         * Templated on the justification type so a RUP justification can carry
         * a typed assertion hint (JustifyUsingRUP{hints::Foo{owner}}) and the
         * up-front contradiction names the constraint it came from, exactly as
         * the constraint's in-search inferences do.
         */
        template <typename Justification_>
        auto install_initial_contradiction(const std::string &, Justification_ why, Reason reason = NoReason{},
            InitialiserPriority priority = InitialiserPriority::SimpleDefinition) -> void
        {
            install_initialiser([why = std::move(why), reason = std::move(reason)](const State &, auto & inference,
                                    ProofLogger * const logger) -> void { inference.contradiction(logger, why, reason); },
                priority);
        }

        ///@}

        /**
         * \name Propagation
         */
        ///@{

        /**
         * Propagate every constraint, until either a fixed point or a contradiction is reached. Every
         * supplied guess seeds the propagation queue with the propagators watching its variable; if no
         * guesses are supplied, requeue every constraint before we start. Pass more than one guess when
         * several changes were applied to the state before propagating (for example a branch decision
         * together with a branch-and-bound objective bound), so that propagators watching any of them are
         * woken.
         */
        [[nodiscard]] auto propagate(const Literals & guesses, State &, ProofLogger * const, std::atomic<bool> * optional_abort_flag = nullptr) const
            -> bool;

        /**
         * Call every initialiser, or until a contradiction is reached.
         */
        [[nodiscard]] auto initialise(State &, ProofLogger * const) const -> bool;

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

        /**
         * How many distinct constraints (by ConstraintID) installed at least
         * one propagator? Equivalently, the number of valid dense constraint
         * indices, which run from zero to this minus one.
         */
        [[nodiscard]] auto number_of_constraints() const -> std::size_t;

        /**
         * The dense constraint index of the propagator with the given id (as
         * supplied to a propagation function and used internally by propagate).
         * Propagators sharing a ConstraintID share an index; indices are
         * assigned densely in order of first sight of each ConstraintID.
         */
        [[nodiscard]] auto constraint_index_of_propagator(int propagator_id) const -> int;

        /**
         * The ConstraintID for a dense constraint index, as returned by
         * constraint_index_of_propagator. The inverse of the first-sight
         * indexing.
         */
        [[nodiscard]] auto constraint_id_for_index(int constraint_index) const -> const ConstraintID &;

        ///@}
    };
}

#endif
