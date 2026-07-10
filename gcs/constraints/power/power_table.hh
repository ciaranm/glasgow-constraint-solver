#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_POWER_POWER_TABLE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_POWER_POWER_TABLE_HH

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

namespace gcs::innards
{
    /**
     * \brief Constrain that base ^ exponent = result via a materialised tuple
     * table, for the variable-exponent case that has no sensible PB encoding.
     *
     * This is the last surviving descendant of the old table-based arithmetic
     * family, and the one deliberate exception to the rule that constraints do
     * not put tuple tables in the OPB (issue #444): a variable exponent is
     * rare enough that it is not worth solving properly. Memory usage is
     * O(|domain(base)| * |domain(exponent)|). Use Power instead, which only
     * comes here when it must.
     *
     * \ingroup Innards
     * \sa Power
     */
    class PowerTable : public Constraint
    {
    private:
        IntegerVariableID _base, _exponent, _result;

    public:
        explicit PowerTable(IntegerVariableID base, IntegerVariableID exponent, IntegerVariableID result);

        virtual auto install(Propagators &, State &, ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const ProofModel * const) const -> SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
