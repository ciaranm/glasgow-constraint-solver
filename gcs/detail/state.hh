/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATE_HH 1

#include <gcs/detail/integer_variable_state.hh>
#include <gcs/detail/justification.hh>
#include <gcs/detail/state-fwd.hh>
#include <gcs/literal.hh>
#include <gcs/problem-fwd.hh>
#include <gcs/current_state.hh>

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

        [[nodiscard]] auto infer_literal_from_direct_integer_variable(
            const DirectIntegerVariableID var,
            LiteralFromIntegerVariable::Operator state,
            Integer value) -> std::pair<Inference, HowChanged>;

        [[nodiscard]] auto assign_to_state_of(const DirectIntegerVariableID) -> IntegerVariableState &;
        [[nodiscard]] auto state_of(const DirectIntegerVariableID, IntegerVariableState & space) -> IntegerVariableState &;
        [[nodiscard]] auto state_of(const DirectIntegerVariableID, IntegerVariableState & space) const -> const IntegerVariableState &;

        auto remember_change(const SimpleIntegerVariableID, HowChanged) -> void;

    public:
        explicit State(const Problem * const problem);
        State(State &&) noexcept;
        ~State();

        State(const State &) = delete;
        auto operator=(const State &) -> State & = delete;

        [[nodiscard]] auto clone() -> State const;

        [[nodiscard]] auto create_integer_variable(Integer lower, Integer upper) -> SimpleIntegerVariableID;
        [[nodiscard]] auto create_pseudovariable(Integer lower, Integer upper, const std::optional<std::string> &) -> SimpleIntegerVariableID;

        [[nodiscard]] auto infer(const Literal & lit, Justification why) -> Inference;
        [[nodiscard]] auto infer_all(const std::vector<Literal> & lit, Justification why) -> Inference;
        auto add_proof_steps(JustifyExplicitly why) -> void;
        [[nodiscard]] auto want_proofs() const -> bool;

        auto guess(const Literal & lit) -> void;
        auto for_each_guess(std::function<auto(Literal)->void>) const -> void;

        [[nodiscard]] auto lower_bound(const IntegerVariableID) const -> Integer;
        [[nodiscard]] auto upper_bound(const IntegerVariableID) const -> Integer;
        [[nodiscard]] auto bounds(const IntegerVariableID) const -> std::pair<Integer, Integer>;
        [[nodiscard]] auto in_domain(const IntegerVariableID, Integer) const -> bool;
        [[nodiscard]] auto optional_single_value(const IntegerVariableID) const -> std::optional<Integer>;
        [[nodiscard]] auto has_single_value(const IntegerVariableID) const -> bool;
        [[nodiscard]] auto domain_size(const IntegerVariableID) const -> Integer;
        auto for_each_value(const IntegerVariableID, std::function<auto(Integer)->void>) const -> void;
        auto for_each_value_while(const IntegerVariableID, std::function<auto(Integer)->bool>) const -> void;
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
