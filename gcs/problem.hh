#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROBLEM_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROBLEM_HH

#include <gcs/constraint.hh>
#include <gcs/exception.hh>
#include <gcs/expression.hh>
#include <gcs/innards/proofs/constraint_proof_model_data.hh>
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
#include <concepts>
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
        [[nodiscard]] auto create_propagators(innards::State &, Stats & stats GCS_LIFETIME_BOUND, innards::ProofModel * const) const
            -> innards::Propagators;

        /**
         * \warning The yielded references alias objects owned by this Problem,
         * and are valid only while the Problem is alive.
         */
        [[nodiscard]] auto each_presolver() const -> std::generator<Presolver &>;

        /**
         * \brief Yields every constraint posted to this Problem so far, in
         * posting order.
         *
         * The yielded object is the clone Problem::post() made, not the caller's
         * instance, and it is never moved from: installation clones again (see
         * create_propagators), so the arguments read back here are exactly what
         * was posted, however many searches have been run over this Problem.
         *
         * \par What a Presolver sees
         *
         * Presolvers run after create_propagators and after the proof model has
         * been finalised (see solve_with in solve.cc), so at Presolver::run time
         * this yields precisely the constraints that were installed as
         * propagators and written to the OPB, and it keeps yielding them for
         * every later presolver: nothing removes a posted constraint. A
         * presolver that posts a *new* constraint will be seen by presolvers
         * that run after it, but that constraint gets no propagator and no OPB
         * row --- both of those doors have already closed --- so a presolver
         * that wants to add propagation must install it into the Propagators it
         * is handed, exactly as AutoTable does.
         *
         * \warning The yielded references alias objects owned by this Problem,
         * and are valid only while the Problem is alive.
         */
        [[nodiscard]] auto each_constraint() const -> std::generator<const Constraint &>;

        /**
         * \brief Yields every posted constraint that is dynamically a
         * `Constraint_`, in posting order: each_constraint() filtered and
         * downcast.
         *
         * This is the enumeration entry point for presolvers that work over a
         * particular constraint shape --- combine it with that constraint's
         * argument accessors, as the difference-logic and Cumulative presolvers
         * do. Everything each_constraint() guarantees about timing and about
         * arguments being as-posted applies here unchanged.
         *
         * \warning Ask for the type Problem *stores*, which is the type
         * Constraint::clone() returns, and which for a constraint family is
         * usually the family's shared base: posting a LessThan stores a
         * ReifiedCompareLessThanOrMaybeEqual and posting a LinearLessThanEqual
         * stores a ReifiedLinearInequality. Asking for the derived,
         * user-facing type is not a compile error, it simply matches nothing.
         * Use the constraint's accessors (typically its reification condition)
         * to tell members of a family apart.
         *
         * \warning The yielded references alias objects owned by this Problem,
         * and are valid only while the Problem is alive.
         */
        template <std::derived_from<Constraint> Constraint_>
        [[nodiscard]] auto each_constraint_of_type() const -> std::generator<const Constraint_ &>
        {
            for (const auto & c : each_constraint())
                if (auto typed = dynamic_cast<const Constraint_ *>(&c))
                    co_yield *typed;
        }

        /**
         * \brief As each_constraint_of_type, but pairing each constraint with
         * the label of the OPB row it publishes, for a caller that means to
         * build proof steps on that row.
         *
         * The label comes from asking the constraint which role names its
         * primary row (innards::ConstraintProofModelData, specialised in the
         * constraint's own header) and then asking the tracker whether a row was
         * emitted under that `(id, role)`. Neither half guesses: a caller that
         * built the label itself would be hard-coding another constraint's
         * naming scheme, which is what this exists to stop.
         *
         * The label is nullopt when the constraint publishes no primary row for
         * the reification kind it was posted with, when no row was emitted under
         * the published role, or when `logger` is null because proofs are off.
         * All three mean the same thing to a caller --- there is nothing to cite,
         * so do not do the thing that would need citing.
         *
         * Asking for a `Constraint_` that has no ConstraintProofModelData
         * specialisation is a compile error naming the type, which is the point:
         * a constraint publishes its stable rows deliberately or not at all.
         *
         * \warning The same warnings as each_constraint_of_type apply: ask for
         * the type Problem *stores*, and the yielded references alias objects
         * owned by this Problem.
         */
        template <std::derived_from<Constraint> Constraint_>
        [[nodiscard]] auto each_constraint_of_type_with_proof_data(const innards::ProofLogger * const logger) const
            -> std::generator<std::pair<const Constraint_ &, std::optional<innards::ProofLineLabel>>>
        {
            for (const auto & c : each_constraint_of_type<Constraint_>()) {
                std::optional<innards::ProofLineLabel> label;
                if (logger) {
                    auto role = innards::ConstraintProofModelData<Constraint_>::primary_row_role(c);
                    if (role)
                        label = innards::constraint_row_label_from(*logger, c.constraint_id(), *role);
                }
                co_yield {c, label};
            }
        }

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
