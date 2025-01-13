#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_LOGGER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_LOGGER_HH

#include <gcs/innards/justification.hh>
#include <gcs/innards/proofs/names_and_ids_tracker-fwd.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_model-fwd.hh>
#include <gcs/innards/proofs/pseudo_boolean.hh>
#include <gcs/innards/proofs/reification.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/proof.hh>

#include <map>
#include <memory>

namespace gcs::innards
{
    using Subproof = std::function<auto(ProofLogger &)->void>;

    enum class ProofRule
    {
        RUP,
        ASSERT,
        IMPLIES,
    };

    class ProofLogger
    {
    private:
        struct Imp;
        std::unique_ptr<Imp> _imp;

        auto record_proof_line(ProofLine line, ProofLevel level) -> ProofLine;

        auto end_proof() -> void;

        auto emit_subproofs(const std::map<std::string, Subproof> & subproofs) -> auto;

    public:
        /**
         * \name Constructors, destructors, and the like.
         */
        ///@{

        explicit ProofLogger(const ProofOptions &, NamesAndIDsTracker &);
        ~ProofLogger();

        auto operator=(const ProofLogger &) -> ProofLogger & = delete;
        ProofLogger(const ProofLogger &) = delete;

        ProofLogger(ProofLogger &&) noexcept;
        auto operator=(ProofLogger &&) noexcept -> ProofLogger &;

        ///@}

        /**
         * Stop writing the OPB file, and start writing the proof. Must be
         * called exactly once, after the proof model is finalised, and
         * before anything else.
         */
        auto start_proof(const ProofModel &) -> void;

        /**
         * Log that a solution has been found.
         */
        auto solution(
            const std::vector<std::pair<IntegerVariableID, Integer>> & all_variables_with_values,
            const std::optional<std::pair<IntegerVariableID, Integer>> & objective_to_minimise) -> void;

        /**
         * Log that we are backtracking.
         */
        auto backtrack(const std::vector<Literal> & guesses) -> void;

        /**
         * Log that we have reached an unsatisfiable conclusion at the end of the proof.
         */
        auto conclude_unsatisfiable(bool is_optimisation) -> void;

        /**
         * Log that we have reached an unsatisfiable conclusion at the end of the proof.
         */
        auto conclude_satisfiable() -> void;

        /**
         * Log that we have reached an optimality conclusion at the end of the proof.
         */
        auto conclude_optimality(IntegerVariableID var, Integer obj) -> void;

        /**
         * Log that we have found some bounds but not proved optimality at the end of the proof.
         */
        auto conclude_bounds(IntegerVariableID var, Integer lower, Integer upper) -> void;

        /**
         * Log that we have not reached a conclusion at the end of the proof.
         */
        auto conclude_none() -> void;

        /**
         * Log, if necessary, that we have inferred a particular literal.
         */
        auto infer(const Literal & lit, const Justification & why, const Reason & reason) -> void;

        /**
         * What is our current proof level?
         */
        [[nodiscard]] auto proof_level() -> int;

        /**
         * Indicate that we will use a temporary proof level, and return it. Must
         * be wiped out with forget_proof_level().
         */
        [[nodiscard]] auto temporary_proof_level() -> int;

        /**
         * Log that we are entering this proof level for deletions.
         */
        auto enter_proof_level(int depth) -> void;

        /**
         * Log that we should delete this proof level.
         */
        auto forget_proof_level(int depth) -> void;

        /**
         * Emit the specified text as a comment.
         */
        auto emit_proof_comment(const std::string &) -> void;

        /**
         * Given a reason, return the vector of literals in the conjunction.
         */
        auto reason_to_lits(const Reason & reason) -> std::vector<ProofLiteralOrFlag>;

        /**
         * Given a PB constraint C and a conjunction of literals L, return the native
         * PB constraint encoding L => C
         */
        auto reified(const WeightedPseudoBooleanLessEqual &, const HalfReifyOnConjunctionOf &) -> WeightedPseudoBooleanLessEqual;

        auto reified(const WeightedPseudoBooleanLessEqual &, const Reason &) -> WeightedPseudoBooleanLessEqual;

        auto weaken_lits(const ProofLine &, std::vector<ProofLiteralOrFlag> lits, ProofLevel level) -> ProofLine;

        /**
         * Emit the specified text as a proof line.
         */
        auto emit_proof_line(const std::string &, ProofLevel level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            const std::source_location & w = std::source_location::current()
#endif
                ) -> ProofLine;

        /**
         * Emit a proof step, with a specified rule.
         */
        auto emit(const ProofRule & rule, const SumLessEqual<Weighted<PseudoBooleanTerm>> &, ProofLevel level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            const std::source_location & w = std::source_location::current()
#endif
                ) -> ProofLine;

        /**
         * Emit a proof step, with a specified rule.
         */
        auto emit_under_reason(const ProofRule & rule, const SumLessEqual<Weighted<PseudoBooleanTerm>> &, ProofLevel level, const Reason &
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            const std::source_location & w = std::source_location::current()
#endif
                ) -> ProofLine;

        /**
         * Emit a proof step, with a specified rule.
         */
        auto emit_under_reason_appending(const ProofRule & rule, const SumLessEqual<Weighted<PseudoBooleanTerm>> &, ProofLevel level, const Reason &,
            const std::optional<ProofLine> & append_line
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            const std::source_location & w = std::source_location::current()
#endif
                ) -> ProofLine;

        /**
         * Emit a RUP proof step for the specified expression, not subject to
         * any reasons.
         */
        auto emit_rup_proof_line(const SumLessEqual<Weighted<PseudoBooleanTerm>> &, ProofLevel level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            const std::source_location & w = std::source_location::current()
#endif
                ) -> ProofLine;

        /**
         * Emit a syntactic implication proof step for the specified expression, not subject to
         * any reasons.
         */
        auto emit_ia_proof_line(const SumLessEqual<Weighted<PseudoBooleanTerm>> &, ProofLevel level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            const std::source_location & w = std::source_location::current()
#endif
                ) -> ProofLine;

        /**
         * Emit an assert proof step for the specified expression, not subject to
         * any reasons.
         */
        auto emit_assert_proof_line(const SumLessEqual<Weighted<PseudoBooleanTerm>> &, ProofLevel level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            const std::source_location & w = std::source_location::current()
#endif
                ) -> ProofLine;

        /**
         * Emit a RUP proof step for the specified expression, subject to a
         * given reason.
         */
        auto emit_rup_proof_line_under_reason(const Reason &, const SumLessEqual<Weighted<PseudoBooleanTerm>> &, ProofLevel level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            const std::source_location & w = std::source_location::current()
#endif
                ) -> ProofLine;

        /**
         * Emit a RUP proof step for the specified expression, subject to a
         * given reason.
         */
        auto emit_ia_proof_line_under_reason(const Reason &, const SumLessEqual<Weighted<PseudoBooleanTerm>> &, ProofLevel level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            const std::source_location & w = std::source_location::current()
#endif
                ) -> ProofLine;

        /**
         * Emit a RUP proof step for the specified expression, subject to a
         * given reason.
         */
        auto emit_ia_proof_line_under_reason(const State &, const Reason &, const SumLessEqual<Weighted<PseudoBooleanTerm>> &, ProofLevel level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            const std::source_location & w = std::source_location::current()
#endif
                ) -> ProofLine;

        /**
         * Emit a RED proof step for the specified expression.
         */
        auto emit_red_proof_line(const SumLessEqual<Weighted<PseudoBooleanTerm>> &,
            const std::vector<std::pair<ProofLiteralOrFlag, ProofLiteralOrFlag>> & witness, ProofLevel level,
            const std::optional<std::map<std::string, Subproof>> & subproofs = std::nullopt
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            const std::source_location & w = std::source_location::current()
#endif
                ) -> ProofLine;

        /**
         * Emit a RED proof step for flag => specified expresion, creating a half reification.
         */
        auto emit_red_proof_lines_forward_reifying(const SumLessEqual<Weighted<PseudoBooleanTerm>> & ineq,
            ProofLiteralOrFlag reif, ProofLevel level, const std::optional<std::map<std::string, Subproof>> & subproof = std::nullopt
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            const std::source_location & w = std::source_location::current()
#endif
                ) -> ProofLine;

        /**
         * Emit a RED proof step for ~flag => ~specified expresion, creating a reverse half reification.
         */
        auto emit_red_proof_lines_reverse_reifying(const SumLessEqual<Weighted<PseudoBooleanTerm>> &,
            ProofLiteralOrFlag, ProofLevel level, const std::optional<std::map<std::string, Subproof>> & subproof = std::nullopt
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            const std::source_location & w = std::source_location::current()
#endif
                ) -> ProofLine;

        /**
         * Emit a pair of RED proofs step for the specified expression, fully reified on the specified flag.
         */
        auto emit_red_proof_lines_reifying(const SumLessEqual<Weighted<PseudoBooleanTerm>> &,
            ProofLiteralOrFlag, ProofLevel level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            const std::source_location & w = std::source_location::current()
#endif
                ) -> std::pair<ProofLine, ProofLine>;

        auto create_proof_flag(const std::string &) -> ProofFlag;

        auto create_proof_flag_reifying(const SumLessEqual<Weighted<PseudoBooleanTerm>> & ineq,
            const std::string & name, ProofLevel level) -> std::tuple<ProofFlag, ProofLine, ProofLine>;

        /**
         * Provide access to information about variables.
         */
        [[nodiscard]] auto names_and_ids_tracker() -> NamesAndIDsTracker &;
    };
}

#endif
