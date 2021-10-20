/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATE_HH 1

#include <gcs/state-fwd.hh>
#include <gcs/integer_variable_state.hh>
#include <gcs/literal.hh>
#include <gcs/problem-fwd.hh>
#include <gcs/justification.hh>

#include <exception>
#include <functional>
#include <memory>
#include <optional>

namespace gcs
{
    auto increase_inference_to(Inference &, const Inference) -> void;

    class VariableDoesNotHaveUniqueValue :
        public std::exception
    {
        private:
            std::string _wat;

        public:
            explicit VariableDoesNotHaveUniqueValue(const std::string &);

            virtual auto what() const noexcept -> const char * override;
    };

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

            [[ nodiscard ]] auto infer_literal_from_direct_integer_variable(
                    const DirectIntegerVariableID var,
                    LiteralFromIntegerVariable::State state,
                    Integer value) -> Inference;

            [[ nodiscard ]] auto assign_to_state_of(const DirectIntegerVariableID) -> IntegerVariableState &;
            [[ nodiscard ]] auto state_of(const DirectIntegerVariableID, IntegerVariableState & space) -> IntegerVariableState &;
            [[ nodiscard ]] auto state_of(const DirectIntegerVariableID, IntegerVariableState & space) const -> const IntegerVariableState &;

            auto remember_change(const SimpleIntegerVariableID) -> void;

        public:
            explicit State(const Problem * const problem);
            State(State &&) noexcept;
            ~State();

            State(const State &) = delete;
            State & operator= (const State &) = delete;

            [[ nodiscard ]] State clone() const;

            [[ nodiscard ]] auto create_integer_variable(Integer lower, Integer upper) -> SimpleIntegerVariableID;
            [[ nodiscard ]] auto create_pseudovariable(Integer lower, Integer upper, const std::optional<std::string> &) -> SimpleIntegerVariableID;

            [[ nodiscard ]] auto infer(const Literal & lit, Justification why) -> Inference;
            [[ nodiscard ]] auto infer_all(const std::vector<Literal> & lit, Justification why) -> Inference;
            auto add_proof_steps(JustifyExplicitly why) -> void;

            auto guess(const Literal & lit) -> void;
            auto for_each_guess(std::function<auto (Literal) -> void>) const -> void;

            [[ nodiscard ]] auto lower_bound(const IntegerVariableID) const -> Integer;
            [[ nodiscard ]] auto upper_bound(const IntegerVariableID) const -> Integer;
            [[ nodiscard ]] auto in_domain(const IntegerVariableID, Integer) const -> bool;
            [[ nodiscard ]] auto optional_single_value(const IntegerVariableID) const -> std::optional<Integer>;
            [[ nodiscard ]] auto has_single_value(const IntegerVariableID) const -> bool;
            [[ nodiscard ]] auto domain_size(const IntegerVariableID) const -> Integer;
            auto for_each_value(const IntegerVariableID, std::function<auto (Integer) -> void>) const -> void;
            auto for_each_value_while(const IntegerVariableID, std::function<auto (Integer) -> bool>) const -> void;
            [[ nodiscard ]] auto domain_has_holes(const IntegerVariableID) const -> bool;

            [[ nodiscard ]] auto test_literal(const Literal &) const -> LiteralIs;
            [[ nodiscard ]] auto literal_is_nonfalsified(const Literal &) const -> bool;

            [[ nodiscard ]] auto operator() (const IntegerVariableID &) const -> Integer;

            [[ nodiscard ]] auto new_epoch() -> Timestamp;
            auto backtrack(Timestamp) -> void;
            auto on_backtrack(std::function<auto () -> void>) -> void;

            auto extract_changed_variables(std::function<auto (SimpleIntegerVariableID) -> void>) -> void;
    };
}

#endif
