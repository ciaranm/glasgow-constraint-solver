#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ARITHMETIC_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ARITHMETIC_HH

#include <gcs/constraint.hh>
#include <gcs/constraints/table.hh>
#include <gcs/variable_id.hh>

namespace gcs
{
    namespace innards
    {
        enum class ArithmeticOperator
        {
            Plus,
            Minus,
            Times,
            Div,
            Mod,
            Power
        };

        /**
         * \brief Arithmetic constraint, constraints that `v1 op v2 = result`.
         *
         * \warning This is a last-resort implementation: it materialises the
         * full list of permitted (v1, v2, result) tuples in memory, so it is
         * O(|domain(v1)| * |domain(v2)|) in space and will exhaust memory for
         * even moderately wide domains.  Prefer one of the dedicated
         * propagators where one exists (see the typedef-specific notes below).
         *
         * \ingroup Constraints
         * \ingroup Innards
         * \sa gcs::Plus
         * \sa gcs::Minus
         * \sa gcs::Times
         * \sa gcs::Div
         * \sa gcs::Mod
         * \sa gcs::Power
         */
        template <ArithmeticOperator op_>
        class GACArithmetic : public Constraint
        {
        private:
            IntegerVariableID _v1, _v2, _result;
            std::unique_ptr<Table> _table;

            virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
            virtual auto define_proof_model(innards::ProofModel &) -> void override;
            virtual auto install_propagators(innards::Propagators &) -> void override;

        public:
            explicit GACArithmetic(const IntegerVariableID v1, const IntegerVariableID v2, const IntegerVariableID result);

            virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
            virtual auto clone() const -> std::unique_ptr<Constraint> override;
            [[nodiscard]] virtual auto s_exprify(const std::string & name, const innards::ProofModel * const) const -> std::string override;
        };
    }

    /**
     * \brief Constrain that `v1 + v2 = result` via a materialised tuple table.
     *
     * \warning Memory usage is O(|domain(v1)| * |domain(v2)|).  Under normal
     * circumstances you should use gcs::Plus, which propagates without
     * enumerating tuples.
     *
     * \ingroup Constraints
     * \sa gcs::Plus
     */
    using PlusGAC = innards::GACArithmetic<innards::ArithmeticOperator::Plus>;

    /**
     * \brief Constrain that `v1 - v2 = result` via a materialised tuple table.
     *
     * \warning Memory usage is O(|domain(v1)| * |domain(v2)|).  Under normal
     * circumstances you should use gcs::Minus, which propagates without
     * enumerating tuples.
     *
     * \ingroup Constraints
     * \sa gcs::Minus
     */
    using MinusGAC = innards::GACArithmetic<innards::ArithmeticOperator::Minus>;

    /**
     * \brief Constrain that `v1 * v2 = result` via a materialised tuple table.
     *
     * \warning Memory usage is O(|domain(v1)| * |domain(v2)|).  Under normal
     * circumstances you should use gcs::LinearEquality if one of the operands
     * is a constant, or gcs::MultBC otherwise.
     *
     * \ingroup Constraints
     * \sa gcs::LinearEquality
     * \sa gcs::MultBC
     */
    using Times = innards::GACArithmetic<innards::ArithmeticOperator::Times>;

    /**
     * \brief Constrain that `v1 / v2 = result`.
     *
     * \warning Memory usage is O(|domain(v1)| * |domain(v2)|): the full tuple
     * table is materialised, so wide variable domains will exhaust memory.
     *
     * \ingroup Constraints
     */
    using Div = innards::GACArithmetic<innards::ArithmeticOperator::Div>;

    /**
     * \brief Constrain that `v1 % v2 = result`.
     *
     * \warning Memory usage is O(|domain(v1)| * |domain(v2)|): the full tuple
     * table is materialised, so wide variable domains will exhaust memory.
     *
     * \ingroup Constraints
     */
    using Mod = innards::GACArithmetic<innards::ArithmeticOperator::Mod>;

    /**
     * \brief Constrain that `power(v1, v2) = result`.
     *
     * \warning Memory usage is O(|domain(v1)| * |domain(v2)|): the full tuple
     * table is materialised, so wide variable domains will exhaust memory.
     *
     * \ingroup Constraints
     */
    using Power = innards::GACArithmetic<innards::ArithmeticOperator::Power>;
}

#endif
