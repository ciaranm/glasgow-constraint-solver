/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATE_HH

#include <gcs/detail/integer_variable_state.hh>
#include <gcs/detail/justification.hh>
#include <gcs/detail/state-fwd.hh>
#include <gcs/detail/variable_id_utils.hh>
#include <gcs/literal.hh>
#include <gcs/problem-fwd.hh>
#include <gcs/current_state.hh>

#include <concepts>
#include <exception>
#include <functional>
#include <memory>
#include <optional>

namespace gcs
{
    auto increase_inference_to(Inference &, const Inference) -> void;

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

    enum class LiteralIs
    {
        DefinitelyFalse,
        DefinitelyTrue,
        Undecided
    };

    class State
    {
    private:
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

        [[nodiscard]] auto assign_to_state_of(const DirectIntegerVariableID) -> IntegerVariableState &;

        [[nodiscard]] auto state_of(const SimpleIntegerVariableID &, IntegerVariableState & space) -> IntegerVariableState &;
        [[nodiscard]] auto state_of(const ConstantIntegerVariableID &, IntegerVariableState & space) -> IntegerVariableState &;
        [[nodiscard]] auto state_of(const DirectIntegerVariableID &, IntegerVariableState & space) -> IntegerVariableState &;

        [[nodiscard]] auto state_of(const SimpleIntegerVariableID &, IntegerVariableState & space) const -> const IntegerVariableState &;
        [[nodiscard]] auto state_of(const ConstantIntegerVariableID &, IntegerVariableState & space) const -> const IntegerVariableState &;
        [[nodiscard]] auto state_of(const DirectIntegerVariableID &, IntegerVariableState & space) const -> const IntegerVariableState &;

        [[nodiscard]] auto state_of(const SimpleIntegerVariableID &) -> IntegerVariableState &;

        [[nodiscard]] auto state_of(const SimpleIntegerVariableID &) const -> const IntegerVariableState &;

        auto prove_and_remember_change(const Inference & inference, const HowChanged & how_changed, const Justification & just,
                const Literal & lit, const DirectIntegerVariableID & actual_var) -> void;

    public:
        explicit State(const Problem * const problem);
        State(State &&) noexcept;
        ~State();

        State(const State &) = delete;
        auto operator=(const State &) -> State & = delete;

        [[nodiscard]] auto clone() const -> State;

        [[nodiscard]] auto create_integer_variable(Integer lower, Integer upper) -> SimpleIntegerVariableID;
        [[nodiscard]] auto create_pseudovariable(Integer lower, Integer upper, const std::optional<std::string> &) -> SimpleIntegerVariableID;

        [[nodiscard]] auto infer(const Literal & lit, const Justification & why) -> Inference;
        [[nodiscard]] auto infer(const LiteralFromIntegerVariable & lit, const Justification & why) -> Inference;

        template <IntegerVariableIDLike VarType_>
        [[nodiscard]] auto infer_equal(const VarType_ &, Integer value, const Justification & why) -> Inference;

        template <IntegerVariableIDLike VarType_>
        [[nodiscard]] auto infer_not_equal(const VarType_ &, Integer value, const Justification & why) -> Inference;

        template <IntegerVariableIDLike VarType_>
        [[nodiscard]] auto infer_less_than(const VarType_ &, Integer value, const Justification & why) -> Inference;

        template <IntegerVariableIDLike VarType_>
        [[nodiscard]] auto infer_greater_than_or_equal(const VarType_ &, Integer value, const Justification & why) -> Inference;

        [[nodiscard]] auto infer_all(const std::vector<Literal> & lit, const Justification & why) -> Inference;
        auto add_proof_steps(JustifyExplicitly why) -> void;
        [[nodiscard]] auto want_proofs() const -> bool;

        auto guess(const Literal & lit) -> void;
        auto for_each_guess(std::function<auto(Literal)->void>) const -> void;

        [[nodiscard]] auto lower_bound(const IntegerVariableID) const -> Integer;
        [[nodiscard]] auto upper_bound(const IntegerVariableID) const -> Integer;

        template <IntegerVariableIDLike VarType_>
        [[nodiscard]] auto in_domain(const VarType_ &, Integer) const -> bool;

        template <IntegerVariableIDLike VarType_>
        [[nodiscard]] auto bounds(const VarType_ &) const -> std::pair<Integer, Integer>;

        template <IntegerVariableIDLike VarType_>
        [[nodiscard]] auto optional_single_value(const VarType_ &) const -> std::optional<Integer>;

        template <IntegerVariableIDLike VarType_>
        [[nodiscard]] auto domain_size(const VarType_ &) const -> Integer;

        [[nodiscard]] auto has_single_value(const IntegerVariableID) const -> bool;

        template <IntegerVariableIDLike VarType_>
        auto for_each_value(const VarType_ &, std::function<auto(Integer)->void>) const -> void;

        template <IntegerVariableIDLike VarType_>
        auto for_each_value_while(const VarType_ &, std::function<auto(Integer)->bool>) const -> void;

        template <IntegerVariableIDLike VarType_>
        auto for_each_value_while_immutable(const VarType_ &, std::function<auto(Integer)->bool>) const -> void;

        [[nodiscard]] auto domain_has_holes(const IntegerVariableID) const -> bool;

        [[nodiscard]] auto test_literal(const Literal &) const -> LiteralIs;
        [[nodiscard]] auto literal_is_nonfalsified(const Literal &) const -> bool;

        [[nodiscard]] auto operator()(const IntegerVariableID &) const -> Integer;

        [[nodiscard]] auto new_epoch() -> Timestamp;
        auto backtrack(Timestamp) -> void;
        auto on_backtrack(std::function<auto()->void>) -> void;

        auto extract_changed_variables(std::function<auto(SimpleIntegerVariableID, HowChanged)->void>) -> void;

        [[nodiscard]] auto current() -> CurrentState;
    };
}

#endif
