#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_POWER_POWER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_POWER_POWER_HH

#include <gcs/consistency.hh>
#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <variant>

namespace gcs
{
    /**
     * \brief The consistency levels supported by Power: consistency::Auto (the
     * default), bounds consistency of the decomposition, or generalised arc
     * consistency by tabulation. A variable exponent is always tabulated.
     *
     * \ingroup Consistency
     */
    using PowerConsistency = std::variant<consistency::Auto, consistency::BC, consistency::Tabulated>;

    /**
     * \brief Constrain that base ^ exponent = result.
     *
     * The semantics follow MiniZinc (and fix a historical disagreement between
     * solvers): 0 ^ 0 = 1; a negative exponent gives 1 div base^|exponent|
     * truncated, so 2 ^ -5 = 0, 1 ^ -n = 1, (-1) ^ -n is 1 or -1 by parity,
     * and 0 ^ -n has no support. A result too big for the solver's integers
     * likewise has no support.
     *
     * A constant exponent dispatches structurally: 0 and 1 are linear
     * equalities, k >= 2 becomes a chain of Multiply constraints over
     * auxiliary variables (with the auxiliaries' ranges clamped by the
     * result's, so a hopeless chain fails rather than overflowing), a negative
     * or enormous exponent becomes a small case analysis on the base. Under
     * consistency::Auto with small domains, or consistency::Tabulated, the whole
     * relation is additionally tabulated in-proof. A variable exponent falls
     * back on innards::PowerTable, the one remaining table-in-the-OPB
     * encoding.
     *
     * \ingroup Constraints
     * \sa Multiply
     * \sa innards::PowerTable
     */
    class Power : public Constraint
    {
    private:
        IntegerVariableID _base, _exponent, _result;
        PowerConsistency _level;

    public:
        explicit Power(IntegerVariableID base, IntegerVariableID exponent, IntegerVariableID result, PowerConsistency level = consistency::Auto{});

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
    };
}

#endif
