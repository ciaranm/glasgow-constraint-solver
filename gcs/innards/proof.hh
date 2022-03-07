/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOF_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOF_HH

#include <gcs/innards/justification.hh>
#include <gcs/innards/linear_utils.hh>
#include <gcs/innards/literal_utils.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/linear.hh>
#include <gcs/literal.hh>
#include <gcs/proof_options.hh>
#include <gcs/variable_id.hh>

#include <exception>
#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief Thrown if something Proof related goes wrong.
     *
     * \ingroup Innards
     */
    class ProofError : public std::exception
    {
    private:
        std::string _wat;

    public:
        explicit ProofError(const std::string &);

        virtual auto what() const noexcept -> const char * override;
    };

    /**
     * \brief A Boolean flag that is used inside proofs like a variable, but
     * that does not appear in the constraint programming model.
     *
     * \ingroup Innards
     */
    struct ProofFlag
    {
        unsigned long long index;
        bool positive;
    };

    /**
     * \brief Negate a ProofFlag.
     *
     * \ingroup Innards
     * \sa ProofFlag
     */
    [[nodiscard]] auto operator!(const ProofFlag &) -> ProofFlag;

    /**
     * \brief Various things in Proof can reify on either a Literal or a ProofFlag.
     *
     * \ingroup Innards
     * \sa Proof::integer_linear_le()
     */
    using ReificationTerm = std::variant<Literal, ProofFlag>;

    /**
     * \brief Inside a Proof, a pseudo-Boolean expression can contain a Literal,
     * a ProofFlag, or an IntegerVariableID to be decomposed into its bits.
     *
     * \ingroup Innards
     * \sa WeightedPseudoBooleanTerm
     * \sa Proof::pseudoboolean_ge
     * \sa gcs::innards::sanitise_pseudoboolean_terms()
     */
    using PseudoBooleanTerm = std::variant<Literal, ProofFlag, IntegerVariableID>;

    /**
     * \brief Inside a Proof, pseudo-Boolean terms are weighted.
     *
     * \ingroup Innards
     * \sa PseudoBooleanTerm
     * \sa Proof::pseudoboolean_ge
     * \sa gcs::innards::sanitise_pseudoboolean_terms()
     */
    using WeightedPseudoBooleanTerm = std::pair<Integer, PseudoBooleanTerm>;

    /**
     * \brief A sequence of weighted pseudo-Boolean terms.
     *
     * \ingroup Innards
     * \sa WeightedPseudoBooleanTerm
     * \sa Proof::pseudoboolean_ge
     * \sa gcs::innards::sanitise_pseudoboolean_terms()
     */
    using WeightedPseudoBooleanTerms = std::vector<WeightedPseudoBooleanTerm>;

    /**
     * \brief Modify a WeightedPseudoBooleanTerms and its associated
     * greater-or-equal inequality value to simplify things.
     *
     * Removes anything that is gcs::innards::is_literally_true_or_false()
     * with appropriate handling of the coefficients.  If false is returned, the
     * expression is trivially satisfied and should not be specified.
     *
     * \ingroup Innards
     * \sa Proof::pseudoboolean_ge
     * \sa WeightedPseudoBooleanTerms
     */
    [[nodiscard]] auto sanitise_pseudoboolean_terms(WeightedPseudoBooleanTerms &, Integer &) -> bool;

    /**
     * \brief Sanitise a Literals by removing duplicates and forced terms.
     *
     * If any term is gcs::innards::is_literally_true(), returns false because
     * the expression is trivially satisfied and should not be specified.
     * Otherwise, removes any gcs::innards::is_literally_false() terms, and
     * groups like terms.
     *
     * \ingroup Innards
     * \sa Proof::cnf
     */
    [[nodiscard]] auto sanitise_literals(Literals &) -> bool;

    /**
     * \brief Everything proof-related goes through here.
     *
     * \ingroup Innards
     */
    class Proof
    {
    private:
        struct Imp;
        std::unique_ptr<Imp> _imp;

        [[nodiscard]] auto xify(std::string &&) -> std::string;

        auto need_gevar(SimpleIntegerVariableID id, Integer v) -> void;

    public:
        /**
         * \name Constructors, destructors, and the like.
         */
        ///@{
        explicit Proof(const ProofOptions &);
        ~Proof();

        auto operator=(const Proof &) -> Proof & = delete;
        Proof(const Proof &) = delete;

        Proof(Proof &&) noexcept;
        auto operator=(Proof &&) noexcept -> Proof &;
        ///@}

        /**
         * \name Define things in the OPB file.
         */
        ///@{

        /**
         * Emit a comment say we're about to define a constraint.
         */
        auto posting(const std::string &) -> void;

        /**
         * Create an integer variable with the specified bounds.
         */
        auto create_integer_variable(SimpleIntegerVariableID, Integer, Integer, const std::optional<std::string> &) -> void;

        /**
         * Create a new ProofFlag, which can be used in various places as if it
         * were a Boolean variable.
         */
        [[nodiscard]] auto create_proof_flag(const std::string &) -> ProofFlag;

        /**
         * Add a new constraint, defined via CNF. Must call gcs::innards::sanitise_literals()
         * first.
         */
        auto cnf(const Literals &) -> ProofLine;

        /**
         * Add an at-most-one constraint.
         */
        [[nodiscard]] auto at_most_one(const Literals &) -> ProofLine;

        /**
         * Add a pseudo-Boolean greater or equals constraint. Must call
         * gcs::innards::sanitise_pseudoboolean_terms() first.
         */
        [[nodiscard]] auto pseudoboolean_ge(const WeightedPseudoBooleanTerms &, Integer) -> ProofLine;

        /**
         * Add an integer linear inequality or equality constraint.
         */
        auto integer_linear_le(const State &, const SimpleLinear & coeff_vars, Integer value,
            std::optional<ReificationTerm> half_reif, bool equality) -> ProofLine;

        /**
         * Specify that this is an optimisation problem, and that we are
         * minimising this variable.
         */
        auto minimise(IntegerVariableID) -> void;

        ///@}

        /**
         * \name Define things either in the OPB file or in the proof log.
         */
        ///@{

        /**
         * Say that we are going to use a Literal in the proof, and that it must
         * be introduced if it is not there already.
         */
        auto need_proof_variable(const Literal &) -> void;

        /**
         * Say that we are going to use the fact that a variable takes a
         * particular value, and that we must have the appropriate Literal
         * available if it is not there already.
         */
        auto need_direct_encoding_for(SimpleIntegerVariableID, Integer) -> void;

        ///@}

        /**
         * \name Proof-related output.
         */
        ///@{

        /**
         * Stop writing the OPB file, and start writing the proof. Must be
         * called exactly once.
         */
        auto start_proof(State & initial_state) -> void;

        /**
         * Log that a solution has been found.
         */
        auto solution(const State &) -> void;

        /**
         * Log that we are backtracking.
         */
        auto backtrack(const State &) -> void;

        /**
         * Log that we have reached a contradiction at the end of the proof.
         */
        auto assert_contradiction() -> void;

        /**
         * Log, if necessary, that we have inferred a particular literal.
         */
        auto infer(const State & state, const Literal & lit, const Justification & why) -> void;

        /**
         * Log that we are entering this proof level for deletions.
         */
        auto enter_proof_level(int depth) -> void;

        /**
         * Log that we should delete this proof level.
         */
        auto forget_proof_level(int depth) -> void;

        /**
         * Add the explicit proof steps given, accumulating lines to be deleted.
         */
        auto add_proof_steps(const JustifyExplicitly &, std::vector<ProofLine> & to_delete) -> void;

        /**
         * Delete the specified proof lines.
         */
        auto delete_proof_lines(const std::vector<ProofLine> & to_delete) -> void;

        /**
         * Emit the specified text as a proof line.
         */
        auto emit_proof_line(const std::string &) -> ProofLine;

        /**
         * Emit the specified text as a comment.
         */
        auto emit_proof_comment(const std::string &) -> void;

        /**
         * Set things up internally as if the specified variable was a real
         * variable, so that proof_variable() etc will work with it.
         */
        auto create_pseudovariable(SimpleIntegerVariableID, Integer, Integer, const std::optional<std::string> &) -> void;

        ///@}

        /**
         * \name Helpful things for making proof text.
         */
        ///@{

        /**
         * Return the sequence of current guesses, formatted for use in a "u"
         * line, each with the given coefficient.
         */
        [[nodiscard]] auto trail_variables(const State &, Integer coeff) -> std::string;

        /**
         * Say that we are going to need an at-least-one constraint for a
         * variable.
         */
        [[nodiscard]] auto need_constraint_saying_variable_takes_at_least_one_value(IntegerVariableID) -> ProofLine;

        /**
         * Return the internal name for the variable corresponding to this
         * Literal. Must call need_proof_variable() first.
         */
        [[nodiscard]] auto proof_variable(const Literal &) const -> const std::string &;

        /**
         * Return the internal name for the variable corresponding to this
         * ProofFlag.
         */
        [[nodiscard]] auto proof_variable(const ProofFlag &) const -> const std::string &;

        /**
         * Give the proof line specifying this variable's upper or lower bound,
         * using the bit representation.
         */
        [[nodiscard]] auto get_or_emit_line_for_bound_in_bits(State & state, bool upper,
            const SimpleIntegerVariableID & var, Integer val) -> ProofLine;

        ///@}

        /**
         * \name Bookkeeping
         */
        ///@{

        /**
         * Called by State to let us know we've made a new guess.
         */
        auto new_guess() -> void;

        /**
         * Called by State to let us know we're backtracking from a guess.
         */
        auto undo_guess() -> void;

        ///@}
    };
}

#endif
