
#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LEX_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LEX_HH

#include <gcs/constraint.hh>
#include <gcs/constraints/innards/reified_state.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/state.hh>
#include <gcs/reification.hh>
#include <gcs/variable_id.hh>

#include <memory>
#include <optional>
#include <vector>

namespace gcs
{
    /**
     * \brief General implementation for lexicographic ordering constraints,
     * including reified and half-reified forms.
     *
     * Internally enforces vars_1 (>|>=)_lex vars_2 — strict or non-strict
     * depending on the `or_equal` flag — under a `ReificationCondition`. The
     * `vars_swapped` flag is a hint to s_exprify about whether the
     * user-facing direction was less-than (less-than variants swap their
     * arguments at construction so the propagator always sees a "greater"
     * problem).
     *
     * Standard lex semantics for unequal-length arrays: when the common
     * prefix is entirely equal, the longer array is the greater one. So
     * `[1,2] <_lex [1,2,0]` and `[1,2,0] >_lex [1,2]` both hold. The two
     * arrays do not need to be the same length.
     *
     * Uses a stateful propagator that maintains the leftmost not-yet-
     * forced-equal position alpha across calls (restored on backtrack via
     * State::add_constraint_state). At each call: advance alpha through any
     * newly-fixed-equal prefix, tighten vars_1[alpha] >= vars_2[alpha], then
     * scan from alpha+1 looking for either a position where strict-greater
     * is feasible (a candidate witness) or a position whose bounds prevent
     * the equal-prefix from extending. Whether "common prefix all equal" is
     * itself a valid outcome depends on the lengths and strictness combined:
     * vars_1 strictly longer always satisfies; equal lengths satisfies only
     * the non-strict variant; vars_1 shorter never satisfies. When that
     * fall-through outcome is invalid (and no later witness is reachable),
     * force strict at alpha.
     *
     * For reified cases, the same alpha-walk is used to detect whether the
     * constraint definitely holds, definitely does not hold, or is still
     * undetermined; the propagator then either forward-propagates the
     * constraint, propagates its negation, or just monitors and infers the
     * reification literal when the constraint state forces it.
     *
     * Proof logging uses a flag-per-position OPB encoding (prefix_equal[i]
     * and decision_at[i] half-reified to vars_1[i] = vars_2[i] and
     * vars_1[i] > vars_2[i] respectively). The global at-least-one
     * disjunction is over decision_at[i] for strict, with prefix_equal[n]
     * additionally allowed for non-strict. For Iff, two encodings are
     * installed (one for the constraint, one for its negation) with
     * separate flag sets, half-reified on the cond and its negation
     * respectively. Inferences emit RUP scaffolding lines via
     * JustifyExplicitlyThenRUP so VeriPB's PB unit propagation can verify
     * each step in isolation.
     *
     * \ingroup Constraints
     * \ingroup Innards
     * \sa LexGreaterThan
     * \sa LexGreaterEqual
     * \sa LexLessThan
     * \sa LexLessThanEqual
     * \sa LexGreaterThanIf
     * \sa LexGreaterThanIff
     * \sa LexGreaterEqualIf
     * \sa LexGreaterEqualIff
     * \sa LexLessThanIf
     * \sa LexLessThanIff
     * \sa LexLessThanEqualIf
     * \sa LexLessThanEqualIff
     */
    class LexCompareGreaterThanOrMaybeEqual : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _vars_1;
        std::vector<IntegerVariableID> _vars_2;
        ReificationCondition _reif_cond;
        bool _or_equal;
        bool _vars_swapped;
        innards::EvaluatedReificationCondition _evaluated_cond = innards::evaluated_reif::Deactivated{};
        innards::ConstraintStateHandle _state_handle;
        std::shared_ptr<std::vector<std::optional<innards::ProofFlag>>> _prefix_equal_gt_flags;
        std::shared_ptr<std::vector<innards::ProofFlag>> _decision_at_gt_flags;
        std::shared_ptr<std::vector<std::optional<innards::ProofFlag>>> _prefix_equal_lt_flags;
        std::shared_ptr<std::vector<innards::ProofFlag>> _decision_at_lt_flags;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit LexCompareGreaterThanOrMaybeEqual(std::vector<IntegerVariableID> vars_1, std::vector<IntegerVariableID> vars_2, ReificationCondition reif_cond, bool or_equal, bool vars_swapped = false);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const std::string & name, const innards::ProofModel * const) const -> std::string override;
    };

    /**
     * \brief Constrain that vars_1 >_lex vars_2 (strict lexicographic greater).
     *
     * \ingroup Constraints
     */
    class LexGreaterThan : public LexCompareGreaterThanOrMaybeEqual
    {
    public:
        inline explicit LexGreaterThan(std::vector<IntegerVariableID> vars_1, std::vector<IntegerVariableID> vars_2) :
            LexCompareGreaterThanOrMaybeEqual(std::move(vars_1), std::move(vars_2), reif::MustHold{}, false, false) {};
    };

    /**
     * \brief Constrain that vars_1 >_lex vars_2 if `cond` holds.
     *
     * \ingroup Constraints
     */
    class LexGreaterThanIf : public LexCompareGreaterThanOrMaybeEqual
    {
    public:
        inline explicit LexGreaterThanIf(std::vector<IntegerVariableID> vars_1, std::vector<IntegerVariableID> vars_2, IntegerVariableCondition cond) :
            LexCompareGreaterThanOrMaybeEqual(std::move(vars_1), std::move(vars_2), reif::If{cond}, false, false) {};
    };

    /**
     * \brief Constrain that vars_1 >_lex vars_2 if and only if `cond` holds.
     *
     * \ingroup Constraints
     */
    class LexGreaterThanIff : public LexCompareGreaterThanOrMaybeEqual
    {
    public:
        inline explicit LexGreaterThanIff(std::vector<IntegerVariableID> vars_1, std::vector<IntegerVariableID> vars_2, IntegerVariableCondition cond) :
            LexCompareGreaterThanOrMaybeEqual(std::move(vars_1), std::move(vars_2), reif::Iff{cond}, false, false) {};
    };

    /**
     * \brief Constrain that vars_1 >=_lex vars_2 (non-strict lexicographic greater or equal).
     *
     * \ingroup Constraints
     */
    class LexGreaterEqual : public LexCompareGreaterThanOrMaybeEqual
    {
    public:
        inline explicit LexGreaterEqual(std::vector<IntegerVariableID> vars_1, std::vector<IntegerVariableID> vars_2) :
            LexCompareGreaterThanOrMaybeEqual(std::move(vars_1), std::move(vars_2), reif::MustHold{}, true, false) {};
    };

    /**
     * \brief Constrain that vars_1 >=_lex vars_2 if `cond` holds.
     *
     * \ingroup Constraints
     */
    class LexGreaterEqualIf : public LexCompareGreaterThanOrMaybeEqual
    {
    public:
        inline explicit LexGreaterEqualIf(std::vector<IntegerVariableID> vars_1, std::vector<IntegerVariableID> vars_2, IntegerVariableCondition cond) :
            LexCompareGreaterThanOrMaybeEqual(std::move(vars_1), std::move(vars_2), reif::If{cond}, true, false) {};
    };

    /**
     * \brief Constrain that vars_1 >=_lex vars_2 if and only if `cond` holds.
     *
     * \ingroup Constraints
     */
    class LexGreaterEqualIff : public LexCompareGreaterThanOrMaybeEqual
    {
    public:
        inline explicit LexGreaterEqualIff(std::vector<IntegerVariableID> vars_1, std::vector<IntegerVariableID> vars_2, IntegerVariableCondition cond) :
            LexCompareGreaterThanOrMaybeEqual(std::move(vars_1), std::move(vars_2), reif::Iff{cond}, true, false) {};
    };

    /**
     * \brief Constrain that vars_1 <_lex vars_2 (strict lexicographic less).
     *
     * \ingroup Constraints
     */
    class LexLessThan : public LexCompareGreaterThanOrMaybeEqual
    {
    public:
        inline explicit LexLessThan(std::vector<IntegerVariableID> vars_1, std::vector<IntegerVariableID> vars_2) :
            LexCompareGreaterThanOrMaybeEqual(std::move(vars_2), std::move(vars_1), reif::MustHold{}, false, true) {};
    };

    /**
     * \brief Constrain that vars_1 <_lex vars_2 if `cond` holds.
     *
     * \ingroup Constraints
     */
    class LexLessThanIf : public LexCompareGreaterThanOrMaybeEqual
    {
    public:
        inline explicit LexLessThanIf(std::vector<IntegerVariableID> vars_1, std::vector<IntegerVariableID> vars_2, IntegerVariableCondition cond) :
            LexCompareGreaterThanOrMaybeEqual(std::move(vars_2), std::move(vars_1), reif::If{cond}, false, true) {};
    };

    /**
     * \brief Constrain that vars_1 <_lex vars_2 if and only if `cond` holds.
     *
     * \ingroup Constraints
     */
    class LexLessThanIff : public LexCompareGreaterThanOrMaybeEqual
    {
    public:
        inline explicit LexLessThanIff(std::vector<IntegerVariableID> vars_1, std::vector<IntegerVariableID> vars_2, IntegerVariableCondition cond) :
            LexCompareGreaterThanOrMaybeEqual(std::move(vars_2), std::move(vars_1), reif::Iff{cond}, false, true) {};
    };

    /**
     * \brief Constrain that vars_1 <=_lex vars_2 (non-strict lexicographic less or equal).
     *
     * \ingroup Constraints
     */
    class LexLessThanEqual : public LexCompareGreaterThanOrMaybeEqual
    {
    public:
        inline explicit LexLessThanEqual(std::vector<IntegerVariableID> vars_1, std::vector<IntegerVariableID> vars_2) :
            LexCompareGreaterThanOrMaybeEqual(std::move(vars_2), std::move(vars_1), reif::MustHold{}, true, true) {};
    };

    /**
     * \brief Constrain that vars_1 <=_lex vars_2 if `cond` holds.
     *
     * \ingroup Constraints
     */
    class LexLessThanEqualIf : public LexCompareGreaterThanOrMaybeEqual
    {
    public:
        inline explicit LexLessThanEqualIf(std::vector<IntegerVariableID> vars_1, std::vector<IntegerVariableID> vars_2, IntegerVariableCondition cond) :
            LexCompareGreaterThanOrMaybeEqual(std::move(vars_2), std::move(vars_1), reif::If{cond}, true, true) {};
    };

    /**
     * \brief Constrain that vars_1 <=_lex vars_2 if and only if `cond` holds.
     *
     * \ingroup Constraints
     */
    class LexLessThanEqualIff : public LexCompareGreaterThanOrMaybeEqual
    {
    public:
        inline explicit LexLessThanEqualIff(std::vector<IntegerVariableID> vars_1, std::vector<IntegerVariableID> vars_2, IntegerVariableCondition cond) :
            LexCompareGreaterThanOrMaybeEqual(std::move(vars_2), std::move(vars_1), reif::Iff{cond}, true, true) {};
    };
}

#endif
