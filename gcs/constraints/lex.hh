
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
     * Kept around alongside Lex for benchmarking and as a reference encoding;
     * for normal use, prefer Lex, which has a dedicated propagator.
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
     * \brief Lexicographic ordering constraint. Enforce vars_1 >_lex vars_2.
     *
     * Uses a stateless two-pass propagator: a left-to-right walk that enforces
     * vars_1[i] >= vars_2[i] while in the forced-equal prefix, plus a
     * right-to-left scan to identify whether strict-greater can still happen
     * later, forcing strict at the first uncertain position when it cannot.
     * The propagator is sound but not GAC; search picks up any unpruned
     * inconsistencies.
     *
     * Proof logging uses a flag-per-position OPB encoding (prefix_equal[i]
     * and decision_at[i] half-reified to vars_1[i] = vars_2[i] and
     * vars_1[i] > vars_2[i] respectively, plus a global at-least-one
     * disjunction over decision_at). Inferences emit RUP scaffolding lines
     * via JustifyExplicitlyThenRUP so VeriPB's PB unit propagation can
     * verify each step in isolation.
     *
     * \ingroup Constraints
     * \sa LexSmartTable
     */
    class Lex : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _vars_1;
        std::vector<IntegerVariableID> _vars_2;

    public:
        explicit Lex(std::vector<IntegerVariableID> vars_1, std::vector<IntegerVariableID> vars_2);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const std::string & name, const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
