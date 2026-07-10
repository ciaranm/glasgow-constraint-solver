#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DIVIDE_MODULUS_DIVIDE_MODULUS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DIVIDE_MODULUS_DIVIDE_MODULUS_HH

#include <gcs/consistency.hh>
#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <variant>

namespace gcs
{
    /**
     * \brief The consistency levels supported by Divide: consistency::Auto
     * (the default), bounds consistency of the decomposition, or generalised
     * arc consistency by tabulation.
     *
     * \ingroup Consistency
     */
    using DivideConsistency = std::variant<consistency::Auto, consistency::BC, consistency::Tabulated>;

    /**
     * \brief The consistency levels supported by Modulus, as for Divide.
     *
     * \ingroup Consistency
     */
    using ModulusConsistency = std::variant<consistency::Auto, consistency::BC, consistency::Tabulated>;

    /**
     * \brief Constrain that x / y = quotient, using truncated integer division
     * (rounding towards zero, like C++ and every constraint programming
     * ecosystem we know of).
     *
     * Division by zero is handled relationally: zero simply has no support in
     * the divisor's domain, so it is pruned, and a constant zero divisor makes
     * the constraint unsatisfiable rather than an error. This matches MiniZinc
     * and XCSP3 semantics.
     *
     * Internally this decomposes as x = quotient * y + r with |r| < |y| and r
     * taking the sign of x (which is what pins truncation: the identity alone
     * does not determine the quotient uniquely for negative operands), with
     * the multiplication going through Multiply's dispatch, so a constant
     * divisor becomes an entirely linear decomposition. Under
     * consistency::Auto with small domains, or consistency::Tabulated, the whole
     * relation is additionally tabulated, with the table derived in-proof so
     * the OPB encoding is unchanged by the choice. Bounds consistency here is
     * with respect to the decomposition, which can be weaker than bounds
     * consistency on the division itself.
     *
     * \ingroup Constraints
     * \sa Modulus
     * \sa Multiply
     */
    class Divide : public Constraint
    {
    private:
        IntegerVariableID _x, _y, _quotient;
        DivideConsistency _level = consistency::Auto{};

    public:
        explicit Divide(IntegerVariableID x, IntegerVariableID y, IntegerVariableID quotient);

        /// Select the consistency level; consistency::Auto (the default) tabulates when the
        /// domains are small. Requesting an unsupported level is a compile-time error.
        auto with_consistency(DivideConsistency level) -> Divide &;

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };

    /**
     * \brief Constrain that x mod y = remainder, where the remainder takes the
     * sign of the dividend x (truncated division semantics, like C++,
     * MiniZinc, and XCSP3).
     *
     * Division by zero is relational, exactly as for Divide, and the
     * decomposition is the same one with the remainder exposed instead of the
     * quotient.
     *
     * \ingroup Constraints
     * \sa Divide
     * \sa Multiply
     */
    class Modulus : public Constraint
    {
    private:
        IntegerVariableID _x, _y, _remainder;
        ModulusConsistency _level = consistency::Auto{};

    public:
        explicit Modulus(IntegerVariableID x, IntegerVariableID y, IntegerVariableID remainder);

        /// Select the consistency level; consistency::Auto (the default) tabulates when the
        /// domains are small. Requesting an unsupported level is a compile-time error.
        auto with_consistency(ModulusConsistency level) -> Modulus &;

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
