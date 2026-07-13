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
#include <cstdint>
#include <functional>
#include <memory>
#include <span>
#include <type_traits>
#include <utility>
#include <vector>

namespace gcs::innards
{
    class ConflictObserver;

    /**
     * \brief Back-channel through which a RefinedWatchContext registers refined
     * watches with the engine.
     *
     * Implemented by the Propagators internals. It exists so that
     * RefinedWatchContext — which appears in propagator function signatures, above
     * the Propagators class — can edit the watch index without depending on it.
     *
     * \ingroup Innards
     */
    class RefinedWatchSink
    {
    public:
        virtual ~RefinedWatchSink() = default;

        /**
         * \brief Arm a refined watch owned by the given propagator: when `literal`
         * next becomes entailed, append `payload` to that propagator's fired set and
         * wake it. Watches armed while propagating are restored on backtrack.
         */
        virtual auto add_refined_watch(int owner_propagator, const Literal & literal, std::uint32_t payload) -> void = 0;

        /**
         * \brief Whether the given propagator currently has any refined watch armed
         * on the given variable. Reads the (backtrack-consistent) watch index, so a
         * propagator can use it to recompute its watched set without keeping its own
         * state. \sa RefinedWatchContext::is_watching
         */
        [[nodiscard]] virtual auto is_watching(int owner_propagator, const IntegerVariableID & var) const -> bool = 0;

        /**
         * \brief Remove every refined watch owned by the given propagator, trailed so
         * backtrack restores them in lockstep with any watches re-armed afterwards.
         * \sa RefinedWatchContext::clear_watches
         */
        virtual auto clear_refined_watches(int owner_propagator) -> void = 0;

        /**
         * \brief Read this propagator's backtrackable scratch value for `key`, or 0
         * if never set. \sa RefinedWatchContext::watch_state
         */
        [[nodiscard]] virtual auto watch_state_get(int owner_propagator, std::uint32_t key) const -> std::uint64_t = 0;

        /**
         * \brief Set this propagator's backtrackable scratch value for `key`. The
         * write is trailed on the same per-propagate() trail as the watch edits and
         * undone on backtrack, so a propagator's own bookkeeping stays in lockstep
         * with its restored watches. \sa RefinedWatchContext::set_watch_state
         */
        virtual auto watch_state_set(int owner_propagator, std::uint32_t key, std::uint64_t value) -> void = 0;
    };

    /**
     * \brief The refined-watch context handed to a propagator each time it runs.
     *
     * A propagator that registers refined per-literal watches (rather than, or in
     * addition to, the coarse \ref Triggers) is told which of its watches fired
     * since it last ran, via the opaque payloads it chose at registration time, so
     * it can do work proportional to what changed instead of rescanning its state.
     * A watch is consumed when it fires; the propagator re-arms a replacement via
     * watch() if it still wants to hear about that literal.
     *
     * The context is forwarded only to propagators whose function accepts it (see
     * PropagationFunctionImpl), so propagators that use only the coarse \ref
     * Triggers are unaffected and see no overhead.
     *
     * \ingroup Innards
     */
    class RefinedWatchContext
    {
    private:
        RefinedWatchSink * _sink = nullptr;
        int _owner = -1;
        std::span<const std::uint32_t> _fired_payloads;

    public:
        RefinedWatchContext() = default;

        RefinedWatchContext(RefinedWatchSink & sink, int owner_propagator, std::span<const std::uint32_t> fired_payloads) :
            _sink(&sink), _owner(owner_propagator), _fired_payloads(fired_payloads)
        {
        }

        /**
         * \brief The payloads of this propagator's refined watches that fired
         * since it last ran, in no particular order.
         *
         * Empty for a propagator that uses only coarse triggers.
         */
        [[nodiscard]] auto fired_payloads() const -> std::span<const std::uint32_t>
        {
            return _fired_payloads;
        }

        /**
         * \brief Arm a refined watch: when `literal` next becomes entailed
         * (test_literal == DefinitelyTrue), this propagator is woken and handed
         * `payload` among its fired_payloads(). A watch registered while
         * propagating is restored on backtrack.
         */
        auto watch(const Literal & literal, std::uint32_t payload) const -> void
        {
            _sink->add_refined_watch(_owner, literal, payload);
        }

        /**
         * \brief Whether this propagator currently has any refined watch armed on
         * `var`. Lets a propagator recompute which variables it should watch each
         * time it runs, without tracking that set itself (which would have to be
         * kept consistent with backtracking); the watch index already is.
         */
        [[nodiscard]] auto is_watching(const IntegerVariableID & var) const -> bool
        {
            return _sink->is_watching(_owner, var);
        }

        /**
         * \brief Drop every refined watch this propagator currently has armed.
         *
         * For a propagator whose natural pattern is to recompute its whole watched
         * set each wake (rather than moving watches individually, like a
         * two-watched-literal clause): clear, then re-arm the fresh set with watch().
         * The removals are trailed like watch(), so backtrack restores exactly the
         * pre-wake watch set. Only variables in the propagator's declared scope (its
         * triggers and scope_only) are searched, so a propagator must watch only
         * variables it has declared in scope -- the intended usage in any case, and
         * what lets degree/adjacency see them. watch_state is independent and left
         * untouched; reset any of it the new watch set no longer matches.
         */
        auto clear_watches() const -> void
        {
            _sink->clear_refined_watches(_owner);
        }

        /**
         * \brief Read this propagator's backtrackable scratch value for `key` (0 if
         * never set). It is restored on backtrack in lockstep with the watches, so a
         * propagator can keep per-watch bookkeeping in it -- e.g. which two positions
         * of a clause it watches -- without having to make that bookkeeping
         * backtrack-consistent itself.
         */
        [[nodiscard]] auto watch_state(std::uint32_t key) const -> std::uint64_t
        {
            return _sink->watch_state_get(_owner, key);
        }

        /// \brief Set this propagator's backtrackable scratch value for `key`.
        auto set_watch_state(std::uint32_t key, std::uint64_t value) const -> void
        {
            _sink->watch_state_set(_owner, key, value);
        }
    };

    class PropagationFunctionImplBase
    {
    public:
        virtual ~PropagationFunctionImplBase() = default;

        PropagationFunctionImplBase() = default;
        PropagationFunctionImplBase(const PropagationFunctionImplBase &) = delete;
        PropagationFunctionImplBase(PropagationFunctionImplBase &&) = default;

        auto operator=(const PropagationFunctionImplBase &) -> PropagationFunctionImplBase & = delete;
        auto operator=(PropagationFunctionImplBase &&) -> PropagationFunctionImplBase & = default;

        [[nodiscard]] virtual auto operator()(const State & state, SimpleInferenceTracker & tracker, ProofLogger * const logger,
            const RefinedWatchContext & watches) -> PropagatorState = 0;
        [[nodiscard]] virtual auto operator()(const State & state, EagerProofLoggingInferenceTracker & tracker, ProofLogger * const logger,
            const RefinedWatchContext & watches) -> PropagatorState = 0;
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

        [[nodiscard]] virtual auto operator()(const State & state, SimpleInferenceTracker & tracker, ProofLogger * const logger,
            [[maybe_unused]] const RefinedWatchContext & watches) -> PropagatorState override
        {
            if constexpr (std::is_invocable_v<Func_ &, const State &, SimpleInferenceTracker &, ProofLogger * const, const RefinedWatchContext &>)
                return _f(state, tracker, logger, watches);
            else
                return _f(state, tracker, logger);
        }

        [[nodiscard]] virtual auto operator()(const State & state, EagerProofLoggingInferenceTracker & tracker, ProofLogger * const logger,
            [[maybe_unused]] const RefinedWatchContext & watches) -> PropagatorState override
        {
            if constexpr (std::is_invocable_v<Func_ &, const State &, EagerProofLoggingInferenceTracker &, ProofLogger * const,
                              const RefinedWatchContext &>)
                return _f(state, tracker, logger, watches);
            else
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

        [[nodiscard]] auto operator()(
            const State & state, SimpleInferenceTracker & tracker, ProofLogger * const logger, const RefinedWatchContext & watches) -> PropagatorState
        {
            return _impl->operator()(state, tracker, logger, watches);
        }

        [[nodiscard]] auto operator()(const State & state, EagerProofLoggingInferenceTracker & tracker, ProofLogger * const logger,
            const RefinedWatchContext & watches) -> PropagatorState
        {
            return _impl->operator()(state, tracker, logger, watches);
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

        /**
         * \brief Refined per-literal watches to arm when the constraint is
         * installed: each (literal, payload) wakes this propagator, handing it
         * payload, when literal first becomes entailed. These install-time watches
         * are the persistent baseline (not undone on backtrack); watches the
         * propagator arms later via RefinedWatchContext::watch are restored on
         * backtrack. \sa RefinedWatchContext
         */
        std::vector<std::pair<Literal, std::uint32_t>> refined = {};

        /**
         * \brief Variables that are in the propagator's scope but arm no wake.
         *
         * A propagator's *scope* — the variables it constrains — is a distinct
         * notion from how it is *woken*. Scope drives each variable's degree (for
         * the dom_then_deg / dom-wdeg branchers), the variable→constraint
         * adjacency, and the idempotence-aliasing check; waking is what the coarse
         * triggers and \ref refined watches do. For an ordinary propagator the two
         * coincide, so listing a variable in on_change/on_bounds/on_instantiated
         * serves both. A propagator woken *only* by refined watches it arms
         * dynamically (its install-time \ref refined and coarse triggers being
         * empty) would otherwise have an empty scope and so be invisible to
         * degree-based heuristics and the aliasing check. List its variables here
         * to declare them in scope without arming a coarse trigger: they raise
         * degree and count as algorithmic positions for aliasing, but generate no
         * wake of their own. \sa RefinedWatchContext
         */
        std::vector<IntegerVariableID> scope_only = {};
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

        /**
         * The scope of the propagator with the given id: its trigger variables
         * (across all trigger kinds) with views resolved to their underlying
         * simple variable and duplicates removed. Indexed by propagator id.
         */
        [[nodiscard]] auto scope_of_propagator(int propagator_id) const -> const std::vector<SimpleIntegerVariableID> &;

        /**
         * The dense constraint indices of every constraint the given variable
         * participates in (it appears in the scope of one of that constraint's
         * propagators), deduplicated. Empty for a variable that no propagator
         * triggers on. This is scope_of_propagator transposed and aggregated by
         * constraint — the adjacency a weighted-degree heuristic sums over.
         */
        [[nodiscard]] auto constraint_indices_of_variable(SimpleIntegerVariableID) const -> const std::vector<int> &;

        /**
         * The scope of the constraint with the given dense index: the union of
         * its propagators' scopes (views resolved, deduplicated). Used to count
         * how many of a constraint's variables are still unassigned (the
         * |fut|>1 filter in a weighted-degree heuristic).
         */
        [[nodiscard]] auto scope_of_constraint(int constraint_index) const -> const std::vector<SimpleIntegerVariableID> &;

        ///@}

        /**
         * \name Conflict observation
         */
        ///@{

        /**
         * Attach a borrowed conflict observer, notified by propagate() whenever
         * a propagator wipes out a domain. The observer is borrowed: the caller
         * owns it and must keep it alive for the duration of the search. A
         * conflict is a Propagators event (it carries the failing constraint's
         * index, scope, and reason, all from here), so the observer lives with
         * the rest of the conflict-observation machinery rather than on State.
         *
         * Several observers may be attached: a seq_search can chain several
         * stateful branchers, each carrying its own weighting, and every one
         * must see every conflict. Each is notified, in the order attached.
         *
         * \sa ConflictObserver
         */
        auto add_conflict_observer(ConflictObserver * observer) -> void;

        /**
         * The conflict observers currently attached, in the order they were
         * added; empty if there are none.
         *
         * \sa Propagators::add_conflict_observer()
         */
        [[nodiscard]] auto conflict_observers() const -> const std::vector<ConflictObserver *> &;

        ///@}
    };
}

#endif
