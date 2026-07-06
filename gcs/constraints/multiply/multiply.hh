#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MULTIPLY_MULTIPLY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MULTIPLY_MULTIPLY_HH

#include <gcs/consistency.hh>
#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <variant>

namespace gcs
{
    /**
     * \brief The consistency levels supported by Multiply: consistency::Auto
     * (the default), bounds consistency, or generalised arc consistency by
     * tabulation.
     *
     * \ingroup Consistency
     */
    using MultiplyConsistency = std::variant<consistency::Auto, consistency::BC, consistency::Tabulated>;

    /**
     * \brief Constrain that v1 * v2 = result.
     *
     * Write multiplication semantically, and the constraint picks an
     * implementation from the shape of its arguments:
     *
     *   - a constant operand collapses the whole thing to a linear equality;
     *   - two variable operands use bounds consistent multiplication over the
     *     actual handles, views and aliases included: a square (x * x = y,
     *     views too) gets exact square and square-root hull filtering on the
     *     true relation, and a result aliasing an operand works directly;
     *   - requesting consistency::Tabulated, or leaving the default
     *     consistency::Auto when the domains involved are small, additionally
     *     tabulates the product relation. The table is derived in-proof, so
     *     this choice never changes the OPB encoding.
     *
     * A product of two different views of one variable (say (x + 1) * (x - 1))
     * is propagated as if the operands were independent, which is weaker than
     * bounds consistency on the quadratic itself; tabulation recovers full
     * strength for small domains.
     *
     * Note that install-time bound computations on very large domains can
     * overflow, and this is an error, unlike the old table-based constraint
     * which would instead attempt to enumerate the cross product of the
     * domains.
     *
     * \ingroup Constraints
     * \sa LinearEquality
     */
    class Multiply : public Constraint
    {
    private:
        IntegerVariableID _v1, _v2, _result;
        MultiplyConsistency _level = consistency::Auto{};

    public:
        explicit Multiply(IntegerVariableID v1, IntegerVariableID v2, IntegerVariableID result);

        /// Select the consistency level; consistency::Auto (the default) tabulates when the
        /// domains are small. Requesting an unsupported level is a compile-time error.
        auto with_consistency(MultiplyConsistency level) -> Multiply &;

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
    };
}

#endif
