/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROBLEM_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROBLEM_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proof-fwd.hh>
#include <gcs/innards/state-fwd.hh>
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
    /**
     * \defgroup Core Core functionality
     */

    /**
     * \brief The central class which defines a constraint satisfaction problem
     * instance to be solved.
     *
     * \ingroup Core
     */
    class Problem
    {
    private:
        struct Imp;
        std::unique_ptr<Imp> _imp;

    public:
        /**
         * \name Constructors, destructors, etc.
         * @{
         */
        Problem();
        explicit Problem(const ProofOptions &);

        ~Problem();

        Problem(const Problem &) = delete;
        Problem & operator=(const Problem &) = delete;

        ///@}

        /**
         * \name For end users.
         *@{
         */

        /**
         * \brief Add this Constraint to the model. This is potentially a
         * destructive operation: the constraint instance will not be valid for
         * further use after this.
         */
        auto post(Constraint &&) -> void;

        /**
         * \brief Create a new integer variable, whose domain goes from lower to
         * upper (inclusive). The final argument gives an optional name that
         * will appear in some output; it does not have to be unique.
         */
        [[nodiscard]] auto create_integer_variable(
            Integer lower,
            Integer upper,
            const std::optional<std::string> & name = std::nullopt) -> SimpleIntegerVariableID;

        /**
         * \brief Create a vector of how_many integer variables, each of
         * whose domain goes from lower to upper (inclusive). The final argument
         * gives an optional name that will appear in some output; it does not
         * have to be unique.
         */
        [[nodiscard]] auto create_integer_variable_vector(
            std::size_t how_many,
            Integer lower,
            Integer upper,
            const std::optional<std::string> & name = std::nullopt) -> std::vector<IntegerVariableID>;

        /**
         * \brief Create n integer variables, each of whose domain goes
         * from lower to upper (inclusive).
         *
         * This should only be used for small values of n, and only for
         * assigning to structured bindings, like
         * ```
         * [ a, b, c ] = create_n_integer_variables<3>(1_i, 3_i);
         * ```
         * Otherwise, use Problem::create_integer_variable_vector instead.
         */
        template <std::size_t n_>
        [[nodiscard]] auto create_n_integer_variables(
            Integer lower,
            Integer upper,
            const std::optional<std::string> & name = std::nullopt) -> std::array<SimpleIntegerVariableID, n_>;

        auto branch_on(const std::vector<IntegerVariableID> &) -> void;

        auto minimise(IntegerVariableID) -> void;
        auto maximise(IntegerVariableID) -> void;

        ///@}

        /**
         * \name For use by the innards.
         * @{
         */

        [[nodiscard]] auto create_state() const -> innards::State;
        [[nodiscard]] auto propagate(innards::State &) const -> bool;

        [[nodiscard]] auto find_branching_variable(innards::State &) const -> std::optional<IntegerVariableID>;

        auto update_objective(const innards::State &) -> void;

        [[nodiscard]] auto optional_proof() const -> std::optional<innards::Proof> &;

        auto fill_in_constraint_stats(Stats &) const -> void;

        ///@}
    };

    namespace innards
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
        innards::ArrayInitialisationMagicForProblem<n_> magic{this, lower, upper, name};
        return magic.result;
    }
}

#endif
