/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATE_HH

#include <gcs/current_state.hh>
#include <gcs/innards/integer_variable_state.hh>
#include <gcs/innards/justification.hh>
#include <gcs/innards/proof-fwd.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/innards/variable_id_utils.hh>
#include <gcs/literal.hh>

#include <concepts>
#include <exception>
#include <functional>
#include <memory>
#include <optional>

namespace gcs::innards
{
    /**
     * \defgroup Innards Solver innards
     */

    /**
     * Increase the first argument until it is at least the second argument.
     *
     * \ingroup Innards
     * \sa Inference
     */
    auto increase_inference_to(Inference &, const Inference) -> void;

    /**
     * \brief Used to indicate a point for backtracking
     *
     * \sa State::guess()
     * \sa State::backtrack()
     * \ingroup Innards
     */
    struct Timestamp
    {
        unsigned long long when;
        unsigned long long how_many_guesses;

        explicit Timestamp(unsigned long long w, unsigned long long g) :
            when(w),
            how_many_guesses(g)
        {
        }
    };

    /**
     * \brief Is a Literal's state known?
     *
     * \sa State::test_literal
     * \ingroup Innards
     */
    enum class LiteralIs
    {
        DefinitelyFalse,
        DefinitelyTrue,
        Undecided
    };

    /**
     * \brief Keeps track of the current state, at a point inside search.
     *
     * This class handles backtracking, and keeping track of which variables
     * have changed for propagation. For end users, part of its API is exposed
     * through the CurrentState class.
     *
     * \ingroup Innards
     * \sa CurrentState
     */
    class State
    {
    private:
        template <typename VarType_>
        struct GetStateAndOffsetOf;

        template <typename VarType_>
        struct GetMutableStateAndOffsetOf;

        struct Imp;
        std::unique_ptr<Imp> _imp;

        template <DirectIntegerVariableIDLike VarType_>
        [[nodiscard]] auto change_state_for_literal(
            const VarType_ & var,
            LiteralFromIntegerVariable::Operator state,
            Integer value) -> std::pair<Inference, HowChanged>;

        template <DirectIntegerVariableIDLike VarType_>
        [[nodiscard]] auto change_state_for_equal(
            const VarType_ & var,
            Integer value) -> std::pair<Inference, HowChanged>;

        template <DirectIntegerVariableIDLike VarType_>
        [[nodiscard]] auto change_state_for_not_equal(
            const VarType_ & var,
            Integer value) -> std::pair<Inference, HowChanged>;

        template <DirectIntegerVariableIDLike VarType_>
        [[nodiscard]] auto change_state_for_less_than(
            const VarType_ & var,
            Integer value) -> std::pair<Inference, HowChanged>;

        template <DirectIntegerVariableIDLike VarType_>
        [[nodiscard]] auto change_state_for_greater_than_or_equal(
            const VarType_ & var,
            Integer value) -> std::pair<Inference, HowChanged>;

        [[nodiscard]] auto assign_to_state_of(const DirectIntegerVariableID) -> innards::IntegerVariableState &;

        [[nodiscard]] auto state_of(const DirectIntegerVariableID &, innards::IntegerVariableState & space) -> innards::IntegerVariableState &;
        [[nodiscard]] auto state_of(const ConstantIntegerVariableID &, innards::IntegerVariableState & space) -> innards::IntegerVariableState &;
        [[nodiscard]] auto state_of(const SimpleIntegerVariableID &) -> innards::IntegerVariableState &;

        [[nodiscard]] auto state_of(const DirectIntegerVariableID &, innards::IntegerVariableState & space) const -> const innards::IntegerVariableState &;
        [[nodiscard]] auto state_of(const ConstantIntegerVariableID &, innards::IntegerVariableState & space) const -> const innards::IntegerVariableState &;
        [[nodiscard]] auto state_of(const SimpleIntegerVariableID &) const -> const innards::IntegerVariableState &;

        auto prove_and_remember_change(const Inference & inference, const HowChanged & how_changed, const Justification & just,
            const Literal & lit, const DirectIntegerVariableID & actual_var) -> void;

    public:
        /**
         * \name Constructors, destructors, etc.
         */
        ///@{

        explicit State(innards::Proof * optional_proof);
        State(State &&) noexcept;
        ~State();

        State(const State &) = delete;
        auto operator=(const State &) -> State & = delete;

        /**
         * Used by Problem::initial_state() to get started. Probably not usable
         * elsewhere without code changes.
         */
        [[nodiscard]] auto clone() const -> State;

        ///@}

        /**
         * \name Variable management.
         */
        ///@{

        /**
         * Used by Problem::create_integer_variable(), which you should be
         * calling instead of this.
         *
         * \sa Problem::create_integer_variable()
         */
        [[nodiscard]] auto create_integer_variable(Integer lower, Integer upper) -> SimpleIntegerVariableID;

        /**
         * Set up something that behaves like a variable in most respects, but
         * that is not a proper variable. Used by some propagators internally.
         */
        [[nodiscard]] auto create_pseudovariable(Integer lower, Integer upper, const std::optional<std::string> &) -> SimpleIntegerVariableID;

        ///@}

        /**
         * \name Inference
         */
        ///@{

        /**
         * Infer that a Literal must hold, for the specified Justification.
         */
        [[nodiscard]] auto infer(const Literal & lit, const Justification & why) -> Inference;

        /**
         * Infer that a Literal must hold, for the specified Justification. Performance overload for if we
         * know we have a LiteralFromIntegerVariable.
         */
        [[nodiscard]] auto infer(const LiteralFromIntegerVariable & lit, const Justification & why) -> Inference;

        /**
         * Infer that a given IntegerVariableID or more specific type must be
         * equal to a particular value. Performance overload of State::infer().
         */
        template <IntegerVariableIDLike VarType_>
        [[nodiscard]] auto infer_equal(const VarType_ &, Integer value, const Justification & why) -> Inference;

        /**
         * Infer that a given IntegerVariableID or more specific type must not
         * equal to a particular value. Performance overload of State::infer().
         */
        template <IntegerVariableIDLike VarType_>
        [[nodiscard]] auto infer_not_equal(const VarType_ &, Integer value, const Justification & why) -> Inference;

        /**
         * Infer that a given IntegerVariableID or more specific type must be less
         * than a particular value. Performance overload of State::infer().
         */
        template <IntegerVariableIDLike VarType_>
        [[nodiscard]] auto infer_less_than(const VarType_ &, Integer value, const Justification & why) -> Inference;

        /**
         * Infer that a given IntegerVariableID or more specific type must be
         * greater than or equal to a particular value. Performance overload of
         * State::infer().
         */
        template <IntegerVariableIDLike VarType_>
        [[nodiscard]] auto infer_greater_than_or_equal(const VarType_ &, Integer value, const Justification & why) -> Inference;

        /**
         * Infer each Literal in turn. If the justification is a
         * JustifyExplicitly, only output its justification once, for the first
         * Literal.
         */
        [[nodiscard]] auto infer_all(const std::vector<Literal> & lit, const Justification & why) -> Inference;

        ///@}

        /**
         * \name Proof-related functions
         */
        ///@{

        /**
         * Output these proof steps, as if we were carrying out an explicit
         * justification. Used by some Constraint implementations that do some
         * non-inference reasoning upon startup.
         */
        auto add_proof_steps(JustifyExplicitly why) -> void;

        /**
         * Do we want proofs?
         */
        [[nodiscard]] auto want_proofs() const -> bool;

        ///@}

        /**
         * \name Branching and guessing.
         */
        ///@{

        /**
         * Guess that the specified Literal holds. Does not deal with
         * backtracking directly.
         *
         * \sa State::new_epoch()
         */
        auto guess(const Literal & lit) -> void;

        /**
         * Call the callback for each active guess in turn.
         *
         * \sa State::guess()
         */
        auto for_each_guess(const std::function<auto(Literal)->void> &) const -> void;

        /**
         * Create a new epoch, that can be backtracked to. Only legal if we are in a fully
         * propagated state, i.e. if extract_changed_variables() would do nothing.
         *
         * \sa State::guess()
         */
        [[nodiscard]] auto new_epoch() -> Timestamp;

        /**
         * Backtrack to the specified Timestamp. Behaviour is currently
         * undefined for anything except nice simple chronological
         * backtracking.
         *
         * \sa State::new_epoch()
         */
        auto backtrack(Timestamp) -> void;

        /**
         * Register a callback that will be called once when we backtrack from
         * the current epoch.
         */
        auto on_backtrack(std::function<auto()->void>) -> void;

        ///@}

        /**
         * \name Optimisation
         */
        ///@{

        /**
         * Update the objective, if we have found a solution.
         */
        auto update_objective_to_current_solution() -> void;

        /**
         * Infer to make the objective variable consistent with the most
         * recently found solution, if necessary.
         *
         * This exists because when backtracking after finding a new incumbent
         * during search, we lose the update to the objective variable.
         */
        [[nodiscard]] auto infer_on_objective_variable_before_propagation() -> Inference;

        /**
         * We're going to be trying to minimise this variable.
         */
        auto minimise(IntegerVariableID) -> void;

        /**
         * We're going to be trying to maximise this variable.
         */
        auto maximise(IntegerVariableID) -> void;

        ///@}

        /**
         * \name Variable state queries.
         */
        ///@{

        /**
         * What is the smallest value in this variable's domain?
         *
         * \sa State::bounds()
         */
        [[nodiscard]] auto lower_bound(const IntegerVariableID) const -> Integer;

        /**
         * What is the largest value in this variable's domain?
         *
         * \sa State::bounds()
         */
        [[nodiscard]] auto upper_bound(const IntegerVariableID) const -> Integer;

        /**
         * Is the specified value present in the variable's domain? Call using
         * either IntegerVariableID or one of its more specific types.
         */
        template <IntegerVariableIDLike VarType_>
        [[nodiscard]] auto in_domain(const VarType_ &, Integer) const -> bool;

        /**
         * What are the smallest and largest values in this variable's domain?
         * Call using either IntegerVariableIDLike or one of its more specific
         * types.
         *
         * \sa State::lower_bound()
         * \sa State::upper_bound()
         */
        template <IntegerVariableIDLike VarType_>
        [[nodiscard]] auto bounds(const VarType_ &) const -> std::pair<Integer, Integer>;

        /**
         * Does this variable have a single value left in its domain, and if
         * so, what is it? Call using either IntegerVariableID or one of its
         * more specific types.
         */
        template <IntegerVariableIDLike VarType_>
        [[nodiscard]] auto optional_single_value(const VarType_ &) const -> std::optional<Integer>;

        /**
         * How many values are left in this variable's domain? Call using
         * either IntegerVariableID or one of its more specific types.
         *
         * \sa State::has_single_value()
         * \sa State::optional_single_value()
         */
        template <IntegerVariableIDLike VarType_>
        [[nodiscard]] auto domain_size(const VarType_ &) const -> Integer;

        /**
         * Does this variable have a single value left in its domain?
         *
         * \sa State::optional_single_value()
         */
        [[nodiscard]] auto has_single_value(const IntegerVariableID) const -> bool;

        /**
         * Call the callback for each value present in a variable's domain. The
         * iterated value may be removed during iteration. Call using either
         * IntegerVariableID or one of its more specific types.
         *
         * \sa State::for_each_value_while()
         * \sa State::for_each_value_while_immutable()
         */
        template <IntegerVariableIDLike VarType_>
        auto for_each_value(const VarType_ &, const std::function<auto(Integer)->void> &) const -> void;

        /**
         * Call the callback for each value present in a variable's domain,
         * stopping if the callback returns false. The iterated value may be
         * removed during iteration. Call using either IntegerVariableID or one
         * of its more specific types. Returns false if the callback ever
         * returns false.
         *
         * \sa State::for_each_value()
         * \sa State::for_each_value_while_immutable()
         */
        template <IntegerVariableIDLike VarType_>
        auto for_each_value_while(const VarType_ &, const std::function<auto(Integer)->bool> &) const -> bool;

        /**
         * Call the callback for each value present in a variable's domain,
         * stopping if the callback returns false. The variable's domain must
         * not be modified by the callback. Call using either IntegerVariableID
         * or one of its more specific types. Returns false if the callback
         * ever returns false.
         *
         * \sa State::for_each_value()
         * \sa State::for_each_value_while()
         */
        template <IntegerVariableIDLike VarType_>
        auto for_each_value_while_immutable(const VarType_ &, const std::function<auto(Integer)->bool> &) const -> bool;

        /**
         * Returns true if this variable's domain is potentially not just
         * contiguous values. May spuriously claim holes are present.
         */
        [[nodiscard]] auto domain_has_holes(const IntegerVariableID) const -> bool;

        /**
         * Is the specified Literal definitely true, definitly false, or unknown?
         *
         * \sa is_literally_true_or_false()
         */
        [[nodiscard]] auto test_literal(const Literal &) const -> LiteralIs;

        /**
         * Is the specified LiteralFromIntegerVariable definitely true,
         * definitly false, or unknown?
         *
         * \sa is_literally_true_or_false()
         */
        [[nodiscard]] auto test_literal(const LiteralFromIntegerVariable &) const -> LiteralIs;

        /**
         * A TrueLiteral is definitely true. Performance overload.
         */
        [[nodiscard]] inline auto test_literal(const TrueLiteral &) const -> LiteralIs
        {
            return LiteralIs::DefinitelyTrue;
        }
        /**
         * A FalseLiteral is definitely true. Performance overload.
         */
        [[nodiscard]] inline auto test_literal(const FalseLiteral &) const -> LiteralIs
        {
            return LiteralIs::DefinitelyFalse;
        }

        /**
         * Return the single value held by this IntegerVariableID, or throw
         * VariableDoesNotHaveUniqueValue.
         *
         * \sa State::optional_single_value()
         * \sa State::has_single_value()
         */
        [[nodiscard]] auto operator()(const IntegerVariableID &) const -> Integer;

        ///@}

        /**
         * \name Propagation and helpers.
         */
        ///@{

        /**
         * Call the associated function once for each variable that has changed
         * since this function was last called, telling us what has happened to
         * it. Used for propagation.
         */
        auto extract_changed_variables(const std::function<auto(SimpleIntegerVariableID, HowChanged)->void> &) -> void;

        ///@}

        /**
         * \name CurrentState related functions
         */
        ///@{

        /**
         * Give a CurrentState of ourself, for passing to end users.
         */
        [[nodiscard]] auto current() -> CurrentState;

        ///@}
    };
}

#endif
