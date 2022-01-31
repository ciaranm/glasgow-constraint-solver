/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROBLEM_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROBLEM_HH 1

#include <gcs/constraint.hh>
#include <gcs/detail/proof-fwd.hh>
#include <gcs/detail/state-fwd.hh>
#include <gcs/literal.hh>
#include <gcs/proof_options.hh>
#include <gcs/stats.hh>
#include <gcs/variable_id.hh>

#include <array>
#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace gcs
{
    class Problem
    {
    private:
        struct Imp;
        std::unique_ptr<Imp> _imp;

    public:
        Problem();
        explicit Problem(const ProofOptions &);

        ~Problem();

        Problem(const Problem &) = delete;
        Problem & operator=(const Problem &) = delete;

        [[nodiscard]] auto create_integer_variable(
            Integer lower,
            Integer upper,
            const std::optional<std::string> & name = std::nullopt) -> SimpleIntegerVariableID;

        [[nodiscard]] auto create_integer_range_variable(
            Integer lower,
            Integer upper,
            const std::optional<std::string> & name = std::nullopt) -> SimpleIntegerVariableID;

        [[nodiscard]] auto create_integer_variable_vector(
            std::size_t how_many,
            Integer lower,
            Integer upper,
            const std::optional<std::string> & name = std::nullopt) -> std::vector<IntegerVariableID>;

        // Probably best to use only for small n, and for assigning using bindings,
        // like [ a, b, c ] = create_integer_variable_array<3>(1_i, 3_i);
        // Use the vector version instead if you don't want to bind directly.
        template <std::size_t n_>
        [[nodiscard]] auto create_n_integer_variables(
            Integer lower,
            Integer upper,
            const std::optional<std::string> & name = std::nullopt) -> std::array<SimpleIntegerVariableID, n_>;

        [[nodiscard]] auto create_state() const -> State;
        [[nodiscard]] auto propagate(State &) const -> bool;

        [[nodiscard]] auto find_branching_variable(State &) const -> std::optional<IntegerVariableID>;

        auto post(Constraint &&) -> void;

        auto branch_on(const std::vector<IntegerVariableID> &) -> void;

        auto minimise(IntegerVariableID) -> void;
        auto update_objective(const State &) -> void;

        [[nodiscard]] auto optional_proof() const -> std::optional<Proof> &;

        auto fill_in_constraint_stats(Stats &) const -> void;
    };

    namespace detail
    {
        template <std::size_t n_>
        struct ArrayInitialisationMagicForProblem
        {
            std::array<SimpleIntegerVariableID, n_> result;

            ArrayInitialisationMagicForProblem(
                Problem * p, Integer l, Integer u, const std::optional<std::string> & name) :
                ArrayInitialisationMagicForProblem(p, l, u, name, std::make_index_sequence<n_>{})
            {
            }

            template <std::size_t... nn_>
            ArrayInitialisationMagicForProblem(
                Problem * p, Integer l, Integer u, const std::optional<std::string> & name, std::index_sequence<nn_...>) :
                result{{p->create_integer_variable(l, u, name ? std::make_optional(*name + std::to_string(nn_)) : std::nullopt)...}}
            {
            }
        };
    }

    template <std::size_t n_>
    auto Problem::create_n_integer_variables(
        Integer lower,
        Integer upper,
        const std::optional<std::string> & name) -> std::array<SimpleIntegerVariableID, n_>
    {
        detail::ArrayInitialisationMagicForProblem<n_> magic{this, lower, upper, name};
        return magic.result;
    }
}

#endif
