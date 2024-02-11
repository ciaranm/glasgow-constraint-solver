#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_LOGGER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_LOGGER_HH

#include <gcs/innards/justification.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_model-fwd.hh>
#include <gcs/innards/proofs/pseudo_boolean.hh>
#include <gcs/innards/proofs/reification.hh>
#include <gcs/innards/proofs/variable_constraints_tracker-fwd.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/proof.hh>

#include <memory>

namespace gcs::innards
{
    class ProofLogger
    {
    private:
        struct Imp;
        std::unique_ptr<Imp> _imp;

        auto record_proof_line(ProofLine line, ProofLevel level) -> ProofLine;

        auto end_proof() -> void;

    public:
        /**
         * \name Constructors, destructors, and the like.
         */
        ///@{

        explicit ProofLogger(const ProofOptions &, VariableConstraintsTracker &);
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
        auto solution(const State &, const std::vector<IntegerVariableID> & all_variables,
            const std::optional<IntegerVariableID> & objective_to_minimise) -> void;

        /**
         * Log that we are backtracking.
         */
        auto backtrack(const State &) -> void;

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
        auto infer(const State & state, bool is_contradicting, const Literal & lit, const Justification & why) -> void;

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
         * Emit the specified text as a proof line.
         */
        auto emit_proof_line(const std::string &, ProofLevel level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            const std::source_location & w = std::source_location::current()
#endif
                ) -> ProofLine;

        /**
         * Emit the specified text as a comment.
         */
        auto emit_proof_comment(const std::string &) -> void;

        /**
         * Emit a RUP proof step for the specified expression, not subject to
         * the current trail.
         */
        auto emit_rup_proof_line(const SumLessEqual<Weighted<PseudoBooleanTerm>> &, ProofLevel level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            const std::source_location & w = std::source_location::current()
#endif
                ) -> ProofLine;

        /**
         * Emit an assert proof step for the specified expression, not subject to
         * the current trail.
         */
        auto emit_assert_proof_line(const SumLessEqual<Weighted<PseudoBooleanTerm>> &, ProofLevel level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            const std::source_location & w = std::source_location::current()
#endif
                ) -> ProofLine;

        /**
         * Emit a RUP proof step for the specified expression, subject to the
         * current trail.
         */
        auto emit_rup_proof_line_under_trail(const State &, const SumLessEqual<Weighted<PseudoBooleanTerm>> &, ProofLevel level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            const std::source_location & w = std::source_location::current()
#endif
                ) -> ProofLine;

        /**
         * Emit a RUP proof step for the specified expression, subject to a
         * given reason.
         */
        auto emit_rup_proof_line_under_reason(const State &, const Reason &, const SumLessEqual<Weighted<PseudoBooleanTerm>> &, ProofLevel level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            const std::source_location & w = std::source_location::current()
#endif
                ) -> ProofLine;

        /**
         * Emit an assert proof step for the specified expression, subject to
         * the current trail.
         */
        auto emit_assert_proof_line_under_trail(const State &, const SumLessEqual<Weighted<PseudoBooleanTerm>> &, ProofLevel level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            const std::source_location & w = std::source_location::current()
#endif
                ) -> ProofLine;

        /**
         * Emit a RED proof step for the specified expression.
         */
        auto emit_red_proof_line(const SumLessEqual<Weighted<PseudoBooleanTerm>> &,
            const std::vector<std::pair<ProofLiteralOrFlag, ProofLiteralOrFlag>> & witness, ProofLevel level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            const std::source_location & w = std::source_location::current()
#endif
                ) -> ProofLine;

        /**
         * Emit a pair of RED proofs step for the specified expression, reified on the specified flag.
         */
        auto emit_red_proof_lines_reifying(const SumLessEqual<Weighted<PseudoBooleanTerm>> &,
            ProofLiteralOrFlag, ProofLevel level
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            const std::source_location & w = std::source_location::current()
#endif
                ) -> std::pair<ProofLine, ProofLine>;

        /**
         * Create a ProofFlag, and emit a RED proof step reifying it for the specified expression.
         */
        auto create_proof_flag_reifying(const SumLessEqual<Weighted<PseudoBooleanTerm>> &,
            const std::string & flag_name, ProofLevel level) -> std::tuple<ProofFlag, ProofLine, ProofLine>;

        /**
         * Provide access to information about variables.
         */
        [[nodiscard]] auto variable_constraints_tracker() -> VariableConstraintsTracker &;
    };
}

#endif
