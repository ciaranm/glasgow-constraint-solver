#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PLUS_MINUS_PLUS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PLUS_MINUS_PLUS_HH

#include <gcs/consistency.hh>
#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <gcs/innards/proofs/proof_logger.hh>

#include <optional>
#include <utility>
#include <variant>

namespace gcs
{
    /**
     * \brief The consistency levels supported by Plus and Minus:
     * consistency::Auto (the default), bounds consistency, or generalised arc
     * consistency by tabulation.
     *
     * \ingroup Consistency
     */
    using PlusConsistency = std::variant<consistency::Auto, consistency::BC, consistency::Tabulated>;

    /**
     * \brief Constrain that a + b = result.
     *
     * The dedicated propagator is bounds consistent; requesting
     * consistency::Tabulated, or leaving the default consistency::Auto with small
     * domains, additionally tabulates the relation, with the table derived
     * in-proof so the OPB encoding is unchanged by the choice.
     *
     * \ingroup Constraints
     */
    class Plus : public Constraint
    {
    private:
        IntegerVariableID _a, _b, _result;
        PlusConsistency _level = consistency::Auto{};
        std::pair<std::optional<innards::ProofLine>, std::optional<innards::ProofLine>> _sum_line;

        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit Plus(IntegerVariableID a, IntegerVariableID b, IntegerVariableID result);

        /// Select the consistency level; consistency::Auto (the default) tabulates when the
        /// domains are small. Requesting an unsupported level is a compile-time error.
        auto with_consistency(PlusConsistency level) -> Plus &;

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
    };
}

#endif
