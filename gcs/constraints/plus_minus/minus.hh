#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PLUS_MINUS_MINUS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PLUS_MINUS_MINUS_HH

#include <gcs/consistency.hh>
#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/variable_id.hh>

#include <optional>
#include <utility>
#include <variant>

namespace gcs
{
    /**
     * \brief Constrain that a - b = result.
     *
     * \ingroup Constraints
     */
    /**
     * \brief The consistency levels supported by Minus, as for Plus.
     *
     * \ingroup Consistency
     */
    using MinusConsistency = std::variant<consistency::Auto, consistency::BC, consistency::Tabulated>;

    class Minus : public Constraint
    {
    private:
        IntegerVariableID _a, _b, _result;
        MinusConsistency _level;
        std::pair<std::optional<innards::ProofLine>, std::optional<innards::ProofLine>> _sum_line;

        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit Minus(IntegerVariableID a, IntegerVariableID b, IntegerVariableID result, MinusConsistency level = consistency::Auto{});

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
    };
}

#endif
