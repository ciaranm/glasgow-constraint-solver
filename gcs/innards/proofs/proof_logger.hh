#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_LOGGER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_LOGGER_HH

#include <gcs/innards/assertion_hints.hh>
#include <gcs/innards/justification.hh>
#include <gcs/innards/proofs/names_and_ids_tracker-fwd.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_model-fwd.hh>
#include <gcs/innards/proofs/pseudo_boolean.hh>
#include <gcs/innards/proofs/reification.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/proof.hh>

#include <map>
#include <memory>
#include <optional>
#include <string>

namespace gcs::innards
{
    using Subproof = std::function<auto(ProofLogger &)->void>;

    struct RUPProofRule
    {
        std::optional<std::vector<ProofLine>> lines;
    };

    struct AssertProofRule
    {
    };

    struct ImpliesProofRule
    {
        std::optional<ProofLine> line;
    };

    using ProofRule = std::variant<RUPProofRule, AssertProofRule, ImpliesProofRule>;

    using ProofGoal = std::variant<ProofLine, std::string>;
    // No ostream operator for ProofGoal: a ProofLine goal is a constraint
    // reference and must be emitted relative to the current line, which needs
    // the logger's counter. ProofLogger::emit_subproofs renders it.

    class ProofLogger
    {
    private:
        struct Imp;
        std::unique_ptr<Imp> _imp;

        auto advance_proof_line_number() -> ProofLineNumber;

        auto record_proof_line(ProofLineNumber line, ProofLevel level) -> ProofLineNumber;

        auto end_proof() -> void;

        auto emit_subproofs(const std::map<ProofGoal, Subproof> & subproofs) -> auto;

        auto log_stacktrace() -> void;

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
        auto solution(const std::vector<std::pair<IntegerVariableID, Integer>> & all_variables_with_values,
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
         * Log that we have found at least one solution, but possibly have not performed a complete search.
         */
        auto conclude_satisfiable() -> void;

        /**
         * Log that we have found at least one solution, and that we have performed a complete search.
         */
        auto conclude_complete_enumeration(Integer number_of_solutions) -> void;

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
         * Log, if necessary, that we have inferred a particular literal. A range
         * conclusion (a NotInRange condition) on a plain, bits-encoded integer
         * variable is a single proof line `~[var in lo..hi] >= 1` emitted under the
         * reason, in place of one `var != v` line per removed value; views and
         * direct-only-encoded variables fall back to per-value emission.
         * Also pass an assertion annotation.
         */
        auto infer(const Literal & lit, const Justification & why, const ReasonLiterals & reason,
            const std::optional<AssertionAnnotation> & annotation = std::nullopt) -> void;

        /**
         * \brief Return the current <em>active proof level</em> &mdash; the
         * integer depth used to tag proof lines.
         *
         * Lines are tagged at one of three depths when emitted:
         * <ul>
         *   <li>\c ProofLevel::Top &rarr; depth 0 (always, regardless of
         *       the active level).</li>
         *   <li>\c ProofLevel::Current &rarr; the active proof level
         *       returned by this function.</li>
         *   <li>\c ProofLevel::Temporary &rarr; one above the active proof
         *       level (\c active_proof_level + 1).</li>
         * </ul>
         *
         * The active level changes as search descends (via
         * \c enter_proof_level) and is restored on backtrack. Use this
         * function to capture and later restore the level in helpers
         * that need to operate at a different depth temporarily.
         */
        [[nodiscard]] auto proof_level() -> int;

        /**
         * \brief Return the depth at which \c ProofLevel::Temporary lines
         * are currently being tagged &mdash; i.e. <em>active proof level +
         * 1</em>.
         *
         * This does <strong>not</strong> push a new level &mdash; it only
         * tells you where Temporary lines will land. To actually push,
         * call \c enter_proof_level(<em>n</em>) with <em>n</em> greater
         * than the current active level.
         *
         * The intended use is the simple emit-then-forget pattern at root:
         * grab \c t = \c temporary_proof_level(), emit some Temporary
         * lines, then call \c forget_proof_level(<em>t</em>) to delete
         * just those. Using this pattern inside a context that itself
         * uses Temporary lines (e.g. inside a \c JustifyExplicitly
         * <tt>{…, ThenRUP::Yes}</tt> callback) is unsafe because the helper's forget will also
         * delete the surrounding context's Temporary lines &mdash;
         * isolate via \c enter_proof_level instead.
         */
        [[nodiscard]] auto temporary_proof_level() -> int;

        /**
         * \brief Set the active proof level to the given depth.
         *
         * Affects how subsequent emissions are tagged: \c Current lines
         * go to the new depth, \c Temporary to depth+1, \c Top still to
         * depth 0. The internal tracking vector is resized to fit if
         * needed.
         *
         * Typical use: temporarily isolate a helper's intermediates from
         * the surrounding scope. Save \c proof_level(); call
         * \c enter_proof_level(<em>saved</em>+1) to push one level deeper;
         * do the work (intermediates record at <em>saved</em>+2 via
         * Temporary); call \c forget_proof_level(<em>saved</em>+2) to
         * delete only the helper's intermediates; call
         * \c enter_proof_level(<em>saved</em>) to restore.
         *
         * The state is a single integer rather than a stack &mdash; the
         * caller is responsible for symmetric restore.
         */
        auto enter_proof_level(int depth) -> void;

        /**
         * \brief Emit deletion commands for every proof line currently
         * tagged at the given depth, then clear the tracking for that
         * depth.
         *
         * Constraints deleted this way can no longer be referenced by
         * later \c pol or \c rup steps &mdash; using a deleted line ID
         * elsewhere in the proof will fail VeriPB at parse time. Top
         * (depth 0) lines should never be forgotten; \c Current and
         * \c Temporary lines are forgotten on backtrack and at the end
         * of explicit-justification scopes respectively.
         */
        auto forget_proof_level(int depth) -> void;

        /**
         * Emit the specified text as a comment.
         */
        auto emit_proof_comment(const std::string &) -> void;

        /**
         * Given a PB constraint C and a conjunction of literals L, return the native
         * PB constraint encoding L => C
         */
        auto reify(const WPBSumLE &, const HalfReifyOnConjunctionOf &) -> WPBSumLE;

        /**
         * Get the current proof line ID (i.e. the next one to be used.
         */
        auto get_current_proof_line() -> ProofLineNumber;

        /**
         * Emit the specified text as a proof line. An optional label is written as a
         * leading `@<label>` (legal before any rule -- pol, rup, red, ia, ...), binding
         * the label to the constraint the line produces, as an OPB `@label` does.
         */
        auto emit_proof_line(const std::string &, ProofLevel level, const std::optional<ProofLineLabel> & label = std::nullopt) -> ProofLine;

        /**
         * Emit a proof step, with a specified rule. An optional label is written as a
         * leading `@<label>` binding it to the constraint the rule adds.
         */
        auto emit(const ProofRule & rule, const SumLessThanEqual<Weighted<PseudoBooleanTerm>> &, ProofLevel level,
            const std::optional<AssertionAnnotation> & assertion_hint = std::nullopt, const std::optional<ProofLineLabel> & label = std::nullopt)
            -> ProofLine;

        /**
         * Emit a proof step, with a specified rule.
         */
        auto emit_under_reason(const ProofRule & rule, const SumLessThanEqual<Weighted<PseudoBooleanTerm>> &, ProofLevel level,
            const ReasonLiterals &, const std::optional<AssertionAnnotation> & assertion_hint = std::nullopt) -> ProofLine;

        /**
         * Emit a RUP proof step for the specified expression, not subject to
         * any reasons.
         */
        auto emit_rup_proof_line(const SumLessThanEqual<Weighted<PseudoBooleanTerm>> &, ProofLevel level) -> ProofLine;

        /**
         * Emit a RUP proof step for the specified expression, subject to a
         * given reason.
         */
        auto emit_rup_proof_line_under_reason(const ReasonLiterals &, const SumLessThanEqual<Weighted<PseudoBooleanTerm>> &, ProofLevel level)
            -> ProofLine;

        /**
         * Emit a `cases` proof step deriving the specified expression by case
         * analysis over `case_flags`, subject to a given reason. VeriPB verifies
         * that, for every assignment to the case flags, the (reason-reified)
         * conclusion follows by RUP, then expands this to plain RUP lines during
         * elaboration. Each branch must be RUP, so this suits selector-style
         * "exactly one of these flags holds" reasoning, not cross-variable
         * cutting-planes case splits.
         */
        auto emit_cases_proof_line_under_reason(const ReasonLiterals &, const SumLessThanEqual<Weighted<PseudoBooleanTerm>> &,
            const std::vector<ProofFlag> & case_flags, ProofLevel level) -> ProofLine;

        /**
         * Like `emit_rup_proof_line_under_reason`, but returns the deview-form
         * line of the just-emitted RUP rather than the V-form line itself.
         *
         * When the input WPBSum has no view operands, the V-form and
         * deview-form coincide, and this is equivalent to the non-deview
         * variant.
         *
         * Use this when a propagator wants to RUP a constraint that
         * mentions a view, and then immediately use that constraint as a
         * pol-side operand. The propagator's pol coefficients were chosen
         * assuming the operand is in deview / "as if the view had been
         * substituted by its underlying" form; without the rewrite, the
         * V-form constraint emitted by the RUP step doesn't match those
         * coefficients and the pol cancellation fails.
         */
        auto emit_rup_proof_line_under_reason_then_deview(
            const ReasonLiterals &, const SumLessThanEqual<Weighted<PseudoBooleanTerm>> &, ProofLevel level) -> ProofLine;

        /**
         * Emit a RED proof step for the specified expression.
         */
        auto emit_red_proof_line(const SumLessThanEqual<Weighted<PseudoBooleanTerm>> &,
            const std::vector<std::pair<ProofLiteralOrFlag, ProofLiteralOrFlag>> & witness, ProofLevel level,
            const std::optional<std::map<ProofGoal, Subproof>> & subproofs = std::nullopt) -> ProofLine;

        /**
         * Emit a RED proof step for flag => specified expresion, creating a half reification.
         */
        auto emit_red_proof_lines_forward_reifying(const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq, ProofLiteralOrFlag reif,
            ProofLevel level, const std::optional<std::map<ProofGoal, Subproof>> & subproof = std::nullopt) -> ProofLine;

        /**
         * Emit a RED proof step for ~flag => ~specified expresion, creating a reverse half reification.
         */
        auto emit_red_proof_lines_reverse_reifying(const SumLessThanEqual<Weighted<PseudoBooleanTerm>> &, ProofLiteralOrFlag, ProofLevel level,
            const std::optional<std::map<ProofGoal, Subproof>> & subproof = std::nullopt) -> ProofLine;

        /**
         * Emit a pair of RED proofs step for the specified expression, fully reified on the specified flag.
         */
        auto emit_red_proof_lines_reifying(const SumLessThanEqual<Weighted<PseudoBooleanTerm>> &, ProofLiteralOrFlag, ProofLevel level)
            -> std::pair<ProofLine, ProofLine>;

        /**
         * \brief Introduce a bits-encoded proof-only variable as equal to a
         * normalized linear form, as a conservative extension --- Wietze Koops's
         * decomposition of the form into bits in 2m redundancy steps (top-down,
         * each bit `e_k <-> running-remainder >= 2^k` as a single-literal-witness
         * red). \c target must have been created with
         * ProofModel::create_proof_only_integer_variable_in_proof, be non-negative,
         * and wide enough that `2^m` exceeds the form's maximum value.
         *
         * Returns `{BinEnc(target) >= form, BinEnc(target) <= form}` --- the last
         * two reds --- so the caller can reference the variable's bound-defining
         * lines (e.g. an end = start + length proxy's end_ge / end_le).
         */
        [[nodiscard]] auto introduce_bits_of(const SumOf<Weighted<PseudoBooleanTerm>> & linear_form, SimpleOrProofOnlyIntegerVariableID target,
            ProofLevel level) -> std::pair<ProofLine, ProofLine>;

        auto create_proof_flag(const std::string &) -> ProofFlag;

        auto create_proof_flag_reifying(const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq, const std::string & name, ProofLevel level)
            -> std::tuple<ProofFlag, ProofLine, ProofLine>;

        /**
         * Provide access to information about variables.
         */
        [[nodiscard]] auto names_and_ids_tracker() -> NamesAndIDsTracker &;

        /**
         * Delete a specified range of ids.
         * NB: This uses half-open range semantics, so "from" is included but "up_to" is excluded.
         */
        auto delete_range(ProofLine from, ProofLine up_to) -> void;

        /**
         * Write a number of spaces equal to current_indent.
         */
        auto write_indent() -> void;

        /**
         * Get the level enum controlling how much of the proof will be asserted
         * instead of fully justified.
         */
        auto get_assertion_level() -> AssertionLevel;
    };
}

#endif
