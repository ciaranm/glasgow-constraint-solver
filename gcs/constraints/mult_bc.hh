#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MULT_BC_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MULT_BC_HH

#include <gcs/constraint.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/state.hh>
#include <gcs/variable_id.hh>

#include <string>

namespace gcs
{

    /**
     * \brief Constrain that v1 * v2 = v3, propagated using bounds consistent multiplication.
     *
     * \ingroup Constraints
     */
    class MultBC : public Constraint
    {
    public:
        struct ChannellingData
        {
            innards::ProofLine pos_ge;
            innards::ProofLine pos_le;
            innards::ProofLine neg_ge;
            innards::ProofLine neg_le;
        };
        MultBC(SimpleIntegerVariableID v1, SimpleIntegerVariableID v2, SimpleIntegerVariableID v3);

        virtual auto install(innards::Propagators & propagators, innards::State &, innards::ProofModel *) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const std::string & name, const innards::ProofModel * const) const -> std::string override;

    private:
        SimpleIntegerVariableID _v1, _v2, _v3;
        Integer _v1_lower = 0_i, _v1_upper = 0_i;
        Integer _v2_lower = 0_i, _v2_upper = 0_i;
        Integer _v3_lower = 0_i, _v3_upper = 0_i;
        innards::ConstraintStateHandle _bit_products_handle;
        std::map<SimpleIntegerVariableID, MultBC::ChannellingData> _channelling_constraints{};
        std::map<SimpleIntegerVariableID, innards::ProofOnlySimpleIntegerVariableID> _mag_var{};
        std::pair<innards::ProofLine, innards::ProofLine> _v3_eq_product_lines;
        virtual auto install_propagators(innards::Propagators &) -> void override;
        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
    };
}

#endif
