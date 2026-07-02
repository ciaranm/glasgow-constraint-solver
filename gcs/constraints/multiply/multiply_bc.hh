#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MULTIPLY_MULTIPLY_BC_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MULTIPLY_MULTIPLY_BC_HH

#include <gcs/constraint.hh>
#include <gcs/innards/literal.hh>
#include <gcs/variable_id.hh>

#include <string>

namespace gcs::innards
{
    /**
     * \brief Constrain that v1 * v2 = v3, propagated using bounds consistent
     * multiplication.
     *
     * This is the implementation behind the two-distinct-variables case of the
     * user-facing Multiply constraint, which is what should usually be posted
     * instead: it requires three distinct genuine variable handles, and throws
     * InvalidProblemDefinitionException on aliased operands (issue #232 tracks
     * lifting that).
     *
     * \ingroup Innards
     * \sa Multiply
     */
    class MultiplyBC : public Constraint
    {
    private:
        SimpleIntegerVariableID _v1, _v2, _v3;

    public:
        MultiplyBC(SimpleIntegerVariableID v1, SimpleIntegerVariableID v2, SimpleIntegerVariableID v3);

        virtual auto install(Propagators & propagators, State &, ProofModel *) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const ProofModel * const) const -> SExpr override;
    };
}

#endif
