#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATE_HH

#include <gcs/current_state.hh>
#include <gcs/innards/integer_variable_state.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/innards/variable_id_utils.hh>

#include <any>
#include <concepts>
#include <exception>
#include <functional>
#include <memory>
#include <optional>

#if __has_cpp_attribute(__cpp_lib_generator)
#include <generator>
#else
#include <__generator.hpp>
#endif

namespace gcs::innards
{
    /**
     * \defgroup Innards Solver innards
     */

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
        std::optional<unsigned long long> how_many_extra_proof_conditions;

        explicit Timestamp(unsigned long long w, unsigned long long g, std::optional<unsigned long long> p) :
            when(w),
            how_many_guesses(g),
            how_many_extra_proof_conditions(p)
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

    using ConstraintState = std::any;

    struct ConstraintStateHandle
    {
        unsigned long index;
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
            VariableConditionOperator op,
            Integer value) -> Inference;

        template <DirectIntegerVariableIDLike VarType_>
        [[nodiscard]] auto change_state_for_equal(
            const VarType_ & var,
            Integer value) -> Inference;

        template <DirectIntegerVariableIDLike VarType_>
        [[nodiscard]] auto change_state_for_not_equal(
            const VarType_ & var,
            Integer value) -> Inference;

        template <DirectIntegerVariableIDLike VarType_>
        [[nodiscard]] auto change_state_for_less_than(
            const VarType_ & var,
            Integer value) -> Inference;

        template <DirectIntegerVariableIDLike VarType_>
        [[nodiscard]] auto change_state_for_greater_than_or_equal(
            const VarType_ & var,
            Integer value) -> Inference;

        [[nodiscard]] inline auto assign_to_state_of(const DirectIntegerVariableID) -> innards::IntegerVariableState &;

        [[nodiscard]] inline auto state_of(const DirectIntegerVariableID &, innards::IntegerVariableState & space) -> innards::IntegerVariableState &;
        [[nodiscard]] inline auto state_of(const ConstantIntegerVariableID &, innards::IntegerVariableState & space) -> innards::IntegerVariableState &;
        [[nodiscard]] inline auto state_of(const SimpleIntegerVariableID &) -> innards::IntegerVariableState &;

        [[nodiscard]] inline auto state_of(const DirectIntegerVariableID &, innards::IntegerVariableState & space) const -> const innards::IntegerVariableState &;
        [[nodiscard]] inline auto state_of(const ConstantIntegerVariableID &, innards::IntegerVariableState & space) const -> const innards::IntegerVariableState &;
        [[nodiscard]] inline auto state_of(const SimpleIntegerVariableID &) const -> const innards::IntegerVariableState &;

    public:
        /**
         * \name Constructors, destructors, etc.
         */
        ///@{

        explicit State();
        State(State &&) noexcept;
        ~State();

        State(const State &) = delete;
        auto operator=(const State &) -> State & = delete;

        /**
         * Used by Problem::initial_state() to get started, and for
         * CurrentState::clone(). Probably not usable elsewhere without code
         * changes.
         */
        [[nodiscard]] auto clone() const -> State;

        ///@}

        /**
         * \name Variable management.
         */
        ///@{

        /**
         * Used by Problem::create_integer_variable(), which you should be
         * calling instead of this. Allocates a new SimpleIntegerVariableID and
         * tracks its state.
         *
         * \sa Problem::create_integer_variable()
         */
        [[nodiscard]] auto allocate_integer_variable_with_state(Integer lower, Integer upper) -> SimpleIntegerVariableID;

        /**
         * Tell us beforehand what the next SimpleIntegerVariableID to be
         * created will be, when we then call
         * create_variable_with_state_but_separate_proof_definition(). Care
         * must be taken when using this because the variable ID returned will
         * not yet be valid.
         */
        [[nodiscard]] auto what_variable_id_will_be_created_next() const -> SimpleIntegerVariableID;

        ///@}

        /**
         * \name Inference
         */
        ///@{

        /**
         * Infer that a Literal must hold.
         */
        [[nodiscard]] auto infer(const Literal & lit) -> Inference;

        /**
         * Infer that a Literal must hold. Performance overload for if we
         * know we have an IntegerVariableCondition.
         */
        template <IntegerVariableIDLike VarType_>
        [[nodiscard]] auto infer(const VariableConditionFrom<VarType_> & lit) -> Inference;

        /**
         * Infer that a given IntegerVariableID or more specific type must be
         * equal to a particular value. Performance overload of State::infer().
         */
        template <IntegerVariableIDLike VarType_>
        [[nodiscard]] auto infer_equal(const VarType_ &, Integer value) -> Inference;

        /**
         * Infer that a given IntegerVariableID or more specific type must not
         * equal to a particular value. Performance overload of State::infer().
         */
        template <IntegerVariableIDLike VarType_>
        [[nodiscard]] auto infer_not_equal(const VarType_ &, Integer value) -> Inference;

        /**
         * Infer that a given IntegerVariableID or more specific type must be less
         * than a particular value. Performance overload of State::infer().
         */
        template <IntegerVariableIDLike VarType_>
        [[nodiscard]] auto infer_less_than(const VarType_ &, Integer value) -> Inference;

        /**
         * Infer that a given IntegerVariableID or more specific type must be
         * greater than or equal to a particular value. Performance overload of
         * State::infer().
         */
        template <IntegerVariableIDLike VarType_>
        [[nodiscard]] auto infer_greater_than_or_equal(const VarType_ &, Integer value) -> Inference;

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
         * Add an additional proof condition, similar to guess except that it
         * does not go away on backtrack unless subsearch is specified. For
         * use in autotabulation and similar.
         */
        auto add_extra_proof_condition(const Literal & lit) -> void;

        /**
         * Return the current set of guesses. Includes any extra proof
         * conditions added using add_extra_proof_condition().
         *
         * \sa State::guess()
         */
        auto guesses() const -> std::generator<Literal>;

        /**
         * Create a new epoch, that can be backtracked to. Only legal if we are in a fully
         * propagated state. If subsearch is true, also clears anything from
         * add_extra_proof_condition() when backtracking.
         *
         * \sa State::guess()
         */
        [[nodiscard]] auto new_epoch(bool subsearch = false) -> Timestamp;

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
         * \sa State::each_value_mutable()
         */
        template <IntegerVariableIDLike VarType_>
        auto for_each_value(const VarType_ &, const std::function<auto(Integer)->void> &) const -> void;

        /**
         * Call the callback for each value present in a variable's domain. The
         * iterated domain must not be modified by the callback. Call using either
         * IntegerVariableID or one of its more specific types.
         *
         * \sa State::for_each_value()
         * \sa State::for_each_value_while_immutable()
         * \sa State::each_value()
         */
        template <IntegerVariableIDLike VarType_>
        auto for_each_value_immutable(const VarType_ &, const std::function<auto(Integer)->void> &) const -> void;

        /**
         * Call the callback for each value present in a variable's domain,
         * stopping if the callback returns false. The iterated value may be
         * removed during iteration. Call using either IntegerVariableID or one
         * of its more specific types. Returns false if the callback ever
         * returns false.
         *
         * \sa State::for_each_value()
         * \sa State::for_each_value_while_immutable()
         * \sa State::each_value()
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
         * \sa State::each_value()
         */
        template <IntegerVariableIDLike VarType_>
        auto for_each_value_while_immutable(const VarType_ &, const std::function<auto(Integer)->bool> &) const -> bool;

        /**
         * Provide a generator that iterates over each value in a variable's
         * domain. The yielded value may be removed during iteration. Call
         * using either IntegerVariableID or one of its more specific types.
         */
        template <IntegerVariableIDLike VarType_>
        auto each_value(const VarType_ &) const -> std::generator<Integer>;

        /**
         * Return the contents of the domain.
         */
        template <IntegerVariableIDLike VarType_>
        auto copy_of_values(const VarType_ &) const -> IntervalSet<Integer>;

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
         * Is the specified IntegerVariableCondition definitely true,
         * definitly false, or unknown?
         *
         * \sa is_literally_true_or_false()
         */
        [[nodiscard]] auto test_literal(const IntegerVariableCondition &) const -> LiteralIs;

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
         * \name CurrentState related functions
         */
        ///@{

        /**
         * Give a CurrentState of ourself, for passing to end users.
         */
        [[nodiscard]] auto current() -> CurrentState;

        ///@}

        /**
         * \name Constraint state related functions.
         */
        ///@{

        /**
         * Store a given std::any value as a constraint state that is accessible via
         * the returned handle and restores on backtrack.
         */
        [[nodiscard]] auto add_constraint_state(const ConstraintState c) -> ConstraintStateHandle;

        /**
         * Store a given std::any value as a constraint state that is accessible via
         * the returned handle and does not restore on backtrack.
         */
        [[nodiscard]] auto add_persistent_constraint_state(const ConstraintState c) -> ConstraintStateHandle;

        /**
         * Return the constraint state for the given handle.
         */
        [[nodiscard]] auto get_constraint_state(const ConstraintStateHandle h) const -> ConstraintState &;

        /**
         * Return the persistent constraint state for the given handle.
         *
         */
        [[nodiscard]] auto get_persistent_constraint_state(const ConstraintStateHandle h) const -> ConstraintState &;

        ///@}
    };
}

#endif
