#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOF_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOF_HH

#include <gcs/innards/justification.hh>
#include <gcs/innards/linear_utils.hh>
#include <gcs/innards/literal_utils.hh>
#include <gcs/innards/proof-fwd.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/literal.hh>
#include <gcs/proof_options.hh>
#include <gcs/variable_id.hh>

#include <exception>
#include <functional>
#include <iosfwd>
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

        [[nodiscard]] auto operator<=>(const ProofFlag &) const = default;
    };

    /**
     * \brief Negate a ProofFlag.
     *
     * \ingroup Innards
     * \sa ProofFlag
     */
    [[nodiscard]] auto operator!(const ProofFlag &) -> ProofFlag;

    /**
     * Behaves similar to a SimpleIntegerVariableID, except only appears
     * in a Proof, with no associated State.
     *
     * \ingroup Innards
     */
    struct ProofOnlySimpleIntegerVariableID
    {
        unsigned long long index;

        explicit ProofOnlySimpleIntegerVariableID(unsigned long long x) :
            index(x)
        {
        }

        [[nodiscard]] auto operator<=>(const ProofOnlySimpleIntegerVariableID &) const = default;
    };

    using SimpleOrProofOnlyIntegerVariableID = std::variant<SimpleIntegerVariableID, ProofOnlySimpleIntegerVariableID>;

    /**
     * \brief Various things in Proof can reify on either a Literal or a ProofFlag.
     *
     * \ingroup Innards
     * \sa Proof::integer_linear_le()
     */
    using ReificationTerm = std::variant<Literal, ProofFlag>;

    /**
     * \brief Inside a Proof, a pseudo-Boolean expression can contain a Literal,
     * a ProofFlag, an IntegerVariableID or ProofOnlySimpleIntegerVariableID
     * to be decomposed into its bits, or if you really want, a raw string
     * (mostly for internal use).
     *
     * \ingroup Innards
     * \sa Proof::pseudoboolean_ge
     */
    using PseudoBooleanTerm = std::variant<Literal, ProofFlag, IntegerVariableID, ProofOnlySimpleIntegerVariableID>;

    using WeightedPseudoBooleanSum = SumOf<Weighted<PseudoBooleanTerm>>;

    using WeightedPseudoBooleanLessEqual = SumLessEqual<Weighted<PseudoBooleanTerm>>;

    using WeightedPseudoBooleanEquality = SumEquals<Weighted<PseudoBooleanTerm>>;

    using SimpleLiteral = std::variant<LiteralFrom<SimpleIntegerVariableID>, TrueLiteral, FalseLiteral>;

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

        auto set_up_bits_variable_encoding(SimpleOrProofOnlyIntegerVariableID, Integer, Integer, const std::string &) -> void;
        auto set_up_direct_only_variable_encoding(SimpleOrProofOnlyIntegerVariableID, Integer, Integer, const std::string &) -> void;

        auto need_all_proof_variables_in(const SumOf<Weighted<PseudoBooleanTerm>> & sum) -> void;

        auto emit_sum_to(const SumOf<Weighted<PseudoBooleanTerm>> & ineq, std::ostream &) -> void;
        auto emit_inequality_to(const SumLessEqual<Weighted<PseudoBooleanTerm>> & ineq,
            const std::optional<ReificationTerm> &, std::ostream &) -> void;

        [[nodiscard]] auto simplify_literal(const Literal & lit) -> SimpleLiteral;

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
         * Set up proof logging for an integer variable with the specified bounds,
         * that is being tracked inside State.
         */
        auto set_up_integer_variable(SimpleIntegerVariableID, Integer, Integer, const std::optional<std::string> &,
            const std::optional<IntegerVariableProofRepresentation> &) -> void;

        /**
         * Create a new ProofFlag, which can be used in various places as if it
         * were a Boolean variable but that is not actually tracked in State.
         */
        [[nodiscard]] auto create_proof_flag(const std::string &) -> ProofFlag;

        /**
         * Create something that behaves like an integer variable for proof purposes,
         * but that does not have any state.
         */
        [[nodiscard]] auto create_proof_integer_variable(Integer, Integer, const std::string &,
            const IntegerVariableProofRepresentation rep) -> ProofOnlySimpleIntegerVariableID;

        /**
         * Add a new constraint, defined via CNF. Returns nullopt if the constraint
         * is trivially satisfiable.
         */
        auto add_cnf_to_model(const Literals &) -> std::optional<ProofLine>;

        /**
         * Add a pseudo-Boolean inequality to the model.
         */
        [[nodiscard]] auto add_to_model(const WeightedPseudoBooleanLessEqual &,
            std::optional<ReificationTerm> half_reif) -> std::optional<ProofLine>;

        /**
         * Add a pseudo-Boolean equality to the model.
         */
        [[nodiscard]] auto add_to_model(const WeightedPseudoBooleanEquality &,
            std::optional<ReificationTerm> half_reif) -> std::pair<std::optional<ProofLine>, std::optional<ProofLine>>;

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
         * Emit a RUP proof step for the specified expression, not subject to
         * the current trail.
         */
        auto emit_rup_proof_line(const SumLessEqual<Weighted<PseudoBooleanTerm>> &) -> ProofLine;

        /**
         * Emit a RUP proof step for the specified expression, subject to the
         * current trail.
         */
        auto emit_rup_proof_line_under_trail(const State &, const SumLessEqual<Weighted<PseudoBooleanTerm>> &) -> ProofLine;

        /**
         * Emit a RED proof step for the specified expression.
         */
        auto emit_red_proof_line(const SumLessEqual<Weighted<PseudoBooleanTerm>> &,
            const std::vector<std::pair<Literal, Literal>> & witness) -> ProofLine;

        /**
         * Set things up internally as if the specified variable was a real
         * variable, so that proof_variable() etc will work with it.
         */
        auto create_literals_for_introduced_variable_value(
            SimpleIntegerVariableID, Integer, const std::optional<std::string> &) -> void;

        ///@}

        /**
         * \name Helpful things for making proof text.
         */
        ///@{

        /**
         * Return the sequence of current guesses, formatted for use in a "u"
         * line, each with the given coefficient.
         */
        [[nodiscard]] auto trail_variables_for_rup(const State &, Integer coeff) -> std::string;

        /**
         * Return the sequence of current guesses, each with the given coefficient.
         */
        [[nodiscard]] auto trail_variables_as_sum(const State &, Integer coeff) -> WeightedPseudoBooleanSum;

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
         * Does a variable have a bit representation?
         */
        [[nodiscard]] auto has_bit_representation(const SimpleIntegerVariableID &) const -> bool;

        /**
         * Give the proof line specifying this variable's upper or lower bound,
         * using the bit representation, or, if this is a literal axiom, return
         * it as a string instead. Only callable if has_bit_representation()
         * returns true.
         */
        [[nodiscard]] auto get_or_emit_pol_term_for_bound_in_bits(State & state, bool upper,
            const SimpleIntegerVariableID & var, Integer val) -> std::variant<ProofLine, std::string>;

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
