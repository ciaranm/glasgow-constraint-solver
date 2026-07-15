#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROBLEM_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROBLEM_HH

#include <gcs/constraint.hh>
#include <gcs/exception.hh>
#include <gcs/expression.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_model-fwd.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/lifetime.hh>
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
#include <version>

#ifdef __cpp_lib_generator
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
     * \brief Thrown if a duplicate or invalid variable name is given.
     *
     * \ingroup Core
     */
    class NamingError : public MessageException
    {
    public:
        explicit NamingError(const std::string &);
    };

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

        [[nodiscard]] auto check_name(const std::string &) -> const std::string &;

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
         * \brief Add a named clone of this Constraint to the model.
         */
        auto post_named(const Constraint &, const std::string &) -> void;

        /**
         * \brief Add a clone of this Constraint that is expected to receive the
         * auto-generated name `_expected_number`.
         *
         * Behaves like post(), but throws NamingError if Problem's own
         * auto-numbering would not assign exactly `_expected_number`. Used when
         * reconstructing a model from its `.scp` (see read_scp): auto-generated
         * `_N` labels can't be passed to post_named (they are reserved), so they
         * are reproduced by re-posting in order, and this checks that the order
         * really does line up rather than silently relabelling.
         */
        auto post_autonumbered(const Constraint &, unsigned long long expected_number) -> void;

        /**
         * \brief Post this expression as a LinearLessThanEqual constraint.
         */
        auto post(SumLessThanEqual<Weighted<IntegerVariableID>>) -> void;

        /**
         * \brief Post this expression as a named LinearLessThanEqual constraint.
         */
        auto post_named(SumLessThanEqual<Weighted<IntegerVariableID>>, const std::string &) -> void;

        /**
         * \brief Post this expression as a LinearEquality constraint.
         */
        auto post(SumEquals<Weighted<IntegerVariableID>>) -> void;

        /**
         * \brief Post this expression as a named LinearEquality constraint.
         */
        auto post_named(SumEquals<Weighted<IntegerVariableID>>, const std::string &) -> void;

        /**
         * \brief Add a clone of this Presolver to the model.
         */
        auto add_presolver(const Presolver &) -> void;

        /**
         * \brief Create a new integer variable, whose domain goes from lower to
         * upper (inclusive). The final argument gives an optional name that
         * will appear in some output; it does not have to be unique.
         *
         * The returned handle is only meaningful for as long as this Problem
         * (or a search state created from it) is alive.
         */
        [[nodiscard]] auto create_integer_variable(Integer lower, Integer upper, const std::optional<std::string> & name = std::nullopt)
            GCS_LIFETIME_BOUND -> SimpleIntegerVariableID;

        /**
         * \brief Create a new integer variable, whose domain is selected from
         * among the chosen values. The final argument gives an optional name that
         * will appear in some output; it does not have to be unique.
         *
         * The returned handle is only meaningful for as long as this Problem
         * (or a search state created from it) is alive.
         */
        [[nodiscard]] auto create_integer_variable(const std::vector<Integer> & domain, const std::optional<std::string> & name = std::nullopt)
            GCS_LIFETIME_BOUND -> SimpleIntegerVariableID;

        /**
         * \brief Create a vector of how_many integer variables, each of
         * whose domain goes from lower to upper (inclusive). The final argument
         * gives an optional name that will appear in some output; it does not
         * have to be unique.
         */
        [[nodiscard]] auto create_integer_variable_vector(std::size_t how_many, Integer lower, Integer upper,
            const std::optional<std::string> & name = std::nullopt) GCS_LIFETIME_BOUND -> std::vector<IntegerVariableID>;

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
        [[nodiscard]] auto create_n_integer_variables(Integer lower, Integer upper, const std::optional<std::string> & name = std::nullopt)
            GCS_LIFETIME_BOUND -> std::array<SimpleIntegerVariableID, n_>;

        auto minimise(IntegerVariableID) -> void;
        auto maximise(IntegerVariableID) -> void;

        /**
         * \brief Returns every integer variable created on this Problem, in
         * creation order.
         *
         * This is the variables made by Problem::create_integer_variable() and
         * friends; it does not include constants, views, or variables created
         * internally by constraints. It is what the search heuristics that
         * take a Problem, such as gcs::variable_order::dom(), branch over.
         *
         * \warning The returned reference is into this Problem, and is valid
         * only for as long as the Problem is alive.
         */
        [[nodiscard]] auto all_normal_variables() const GCS_LIFETIME_BOUND -> const std::vector<IntegerVariableID> &;

        ///@}

        /**
         * \name For use by the innards.
         *
         * These members are public because the solving machinery, proof
         * writers, and search heuristics live in other classes and namespaces,
         * but they are not part of the stable end-user API: they may change or
         * disappear without notice. See issue #289 for the policy.
         *
         * @{
         */

        /**
         * \brief Create a fresh state for a new search, returned by value.
         */
        [[nodiscard]] auto create_state_for_new_search(innards::ProofModel * const) const -> innards::State;

        /**
         * \brief Create the propagators for a search over this Problem,
         * returned by value.
         */
        [[nodiscard]] auto create_propagators(innards::State &, innards::ProofModel * const) const -> innards::Propagators;

        /**
         * \warning The yielded references alias objects owned by this Problem,
         * and are valid only while the Problem is alive.
         */
        [[nodiscard]] auto each_presolver() const -> std::generator<Presolver &>;

        /**
         * \warning The yielded references alias objects owned by this Problem,
         * and are valid only while the Problem is alive.
         */
        [[nodiscard]] auto each_constraint() const -> std::generator<const Constraint &>;

        /**
         * \brief Returns a generator giving each variable together with its
         * bounds and its name, all yielded by value.
         */
        [[nodiscard]] auto each_variable_with_bounds_and_name() const -> std::generator<std::tuple<IntegerVariableID, Integer, Integer, std::string>>;

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

            ArrayInitialisationMagicForProblem(Problem * p, Integer l, Integer u, const std::optional<std::string> & name) :
                ArrayInitialisationMagicForProblem(p, l, u, name, std::make_index_sequence<n_>{})
            {
            }

            template <std::size_t... nn_>
            ArrayInitialisationMagicForProblem(
                Problem * p, Integer l, Integer u, const std::optional<std::string> & name, std::index_sequence<nn_...>) :
                result{
                    {p->create_integer_variable(l, u, name.transform([&](const std::string & s) { return s + "[" + std::to_string(nn_) + "]"; }))...}}
            {
            }
        };
    }

    template <std::size_t n_>
    auto Problem::create_n_integer_variables(Integer lower, Integer upper, const std::optional<std::string> & name)
        -> std::array<SimpleIntegerVariableID, n_>
    {
        innards::ArrayInitialisationMagicForProblem<n_> magic{this, lower, upper, name};
        return magic.result;
    }
}

#endif
