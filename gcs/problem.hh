#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROBLEM_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROBLEM_HH

#include <gcs/constraint.hh>
#include <gcs/expression.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_model-fwd.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/presolver.hh>
#include <gcs/proof.hh>
#include <gcs/stats.hh>
#include <gcs/variable_condition.hh>
#include <gcs/variable_id.hh>

#include <array>
#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#if __has_cpp_attribute(__cpp_lib_generator)
#include <generator>
#else
#include <__generator.hpp>
#endif

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

        ~Problem();

        Problem(const Problem &) = delete;
        Problem & operator=(const Problem &) = delete;

        ///@}

        /**
         * \name For end users.
         *@{
         */

        /**
         * \brief Add a clone of this Constraint to the model.
         */
        auto post(const Constraint &) -> void;

        /**
         * \brief Post this expression as a LinearLessEqual constraint.
         */
        auto post(SumLessEqual<Weighted<IntegerVariableID>>) -> void;

        /**
         * \brief Post this expression as a LinearEquality constraint.
         */
        auto post(SumEquals<Weighted<IntegerVariableID>>) -> void;

        /**
         * \brief Add a clone of this Presolver to the model.
         */
        auto add_presolver(const Presolver &) -> void;

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
         * \brief Create a new integer variable, whose domain is selected from
         * among the chosen values. The final argument gives an optional name that
         * will appear in some output; it does not have to be unique.
         */
        [[nodiscard]] auto create_integer_variable(
            const std::vector<Integer> & domain,
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

        auto minimise(IntegerVariableID) -> void;
        auto maximise(IntegerVariableID) -> void;

        ///@}

        /**
         * \name For use by the innards.
         * @{
         */

        [[nodiscard]] auto create_state_for_new_search(
            innards::ProofModel * const) const -> innards::State;

        [[nodiscard]] auto create_propagators(innards::State &, innards::ProofModel * const) const -> innards::Propagators;

        [[nodiscard]] auto for_each_presolver(const std::function<auto(Presolver &)->bool> &) const -> bool;

        auto all_normal_variables() const -> const std::vector<IntegerVariableID> &;

        [[nodiscard]] auto each_constraint() const -> std::generator<const Constraint &>;

        [[nodiscard]] auto each_variable_with_bounds_and_name() const -> std::generator<
                                                                          std::tuple<IntegerVariableID, Integer, Integer, std::string>>;

        /**
         * What is our objective variable, to minimise?
         */
        [[nodiscard]] auto optional_minimise_variable() const -> std::optional<IntegerVariableID>;

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
