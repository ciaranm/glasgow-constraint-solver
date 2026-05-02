
#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LEX_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LEX_HH

#include <gcs/constraint.hh>
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
     * \brief General implementation for lexicographic ordering constraints.
     *
     * Internally enforces vars_1 (>|>=)_lex vars_2 — strict or non-strict
     * depending on the `or_equal` flag. The `vars_swapped` flag is a hint
     * to s_exprify about whether the user-facing direction was less-than
     * (variants swap their arguments at construction so the propagator
     * always sees a "greater" problem).
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
     * Proof logging uses a flag-per-position OPB encoding (prefix_equal[i]
     * and decision_at[i] half-reified to vars_1[i] = vars_2[i] and
     * vars_1[i] > vars_2[i] respectively). The global at-least-one
     * disjunction is over decision_at[i] for strict, with prefix_equal[n]
     * additionally allowed for non-strict (so an all-equal assignment
     * satisfies the constraint). Inferences emit RUP scaffolding lines via
     * JustifyExplicitlyThenRUP so VeriPB's PB unit propagation can verify
     * each step in isolation.
     *
     * \ingroup Constraints
     * \ingroup Innards
     * \sa LexGreaterThan
     * \sa LexGreaterEqual
     * \sa LexLessThan
     * \sa LexLessThanEqual
     * \sa LexSmartTable
     */
    class LexCompareGreaterThanOrMaybeEqual : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _vars_1;
        std::vector<IntegerVariableID> _vars_2;
        bool _or_equal;
        bool _vars_swapped;

    public:
        explicit LexCompareGreaterThanOrMaybeEqual(std::vector<IntegerVariableID> vars_1, std::vector<IntegerVariableID> vars_2, bool or_equal, bool vars_swapped = false);

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
            LexCompareGreaterThanOrMaybeEqual(std::move(vars_1), std::move(vars_2), false, false) {};
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
            LexCompareGreaterThanOrMaybeEqual(std::move(vars_1), std::move(vars_2), true, false) {};
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
            LexCompareGreaterThanOrMaybeEqual(std::move(vars_2), std::move(vars_1), false, true) {};
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
            LexCompareGreaterThanOrMaybeEqual(std::move(vars_2), std::move(vars_1), true, true) {};
    };
}

#endif
