
#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LEX_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LEX_HH

#include <gcs/constraint.hh>
#include <gcs/reification.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief Lexicographic ordering constraint, encoded as a SmartTable.
     * Enforce vars_1 >_lex vars_2.
     *
     * Kept around alongside LexGreaterThan for benchmarking and as a
     * reference encoding; for normal use, prefer one of the dedicated
     * Lex* constraints, which share a single propagator.
     *
     * \ingroup Constraints
     */
    class LexSmartTable : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _vars_1;
        std::vector<IntegerVariableID> _vars_2;

    public:
        explicit LexSmartTable(std::vector<IntegerVariableID> vars_1, std::vector<IntegerVariableID> vars_2);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const std::string & name, const innards::ProofModel * const) const -> std::string override;
    };

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
     * Uses a stateful propagator that maintains the leftmost not-yet-
     * forced-equal position alpha across calls (restored on backtrack via
     * State::add_constraint_state). At each call: advance alpha through any
     * newly-fixed-equal prefix, tighten vars_1[alpha] >= vars_2[alpha], then
     * scan from alpha+1 looking for either a position where strict-greater
     * is feasible (a candidate witness) or a position whose bounds prevent
     * the equal-prefix from extending. For strict (`!or_equal`), force
     * strict at alpha whenever no later witness is reachable; for
     * non-strict, only force strict when the equal-prefix cannot extend
     * to the end (since otherwise all-equal is itself a valid solution).
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
     * \sa LexSmartTable
     */
    class LexCompareGreaterThanOrMaybeEqual : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _vars_1;
        std::vector<IntegerVariableID> _vars_2;
        ReificationCondition _reif_cond;
        bool _or_equal;
        bool _vars_swapped;

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
