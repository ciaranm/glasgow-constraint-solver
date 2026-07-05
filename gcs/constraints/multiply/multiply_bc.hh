#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MULTIPLY_MULTIPLY_BC_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MULTIPLY_MULTIPLY_BC_HH

#include <gcs/constraint.hh>
#include <gcs/constraint_id.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_model-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/state.hh>
#include <gcs/variable_id.hh>

#include <map>
#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief The bounds consistent multiplication machinery, exposed so that
     * compound constraints (Multiply's decomposed paths, Divide, Modulus,
     * Power's chains) can emit the encoding into their own OPB block and call
     * the propagation from their own propagator, rather than installing a
     * child constraint (issue #448).
     *
     * \ingroup Innards
     */
    namespace mult_bc
    {
        struct BitProductData
        {
            ProofFlag flag;
            ProofLine forwards_reif;
            ProofLine reverse_reif;
            std::optional<ProofLine> partial_product_1;
            std::optional<ProofLine> partial_product_2;
        };

        struct ChannellingData
        {
            ProofLine pos_ge;
            ProofLine pos_le;
            ProofLine neg_ge;
            ProofLine neg_le;
            // The magnitude channel is gated on the reified sign atom [v>=0]
            // (cake_pb_cp's scheme) rather than the two's-complement sign bit
            // (the legacy scheme); channel_to_sign_bit reifies accordingly.
            bool ge0_gated = false;
            // Whether the operand's own encoding can take negative values (its
            // initial domain included negatives, so it has a sign bit). In the
            // legacy scheme channelling <=> signed, but cake channels every operand
            // including non-negative ones, so the quotient reasoning reads this to
            // pick the operand's outer bit-range rather than assuming non-negative.
            bool has_negatives = false;
        };

        /**
         * \brief Everything the propagation's justifications need to know
         * about the encoding define_encoding() emitted. Default-constructed
         * (empty) when proofs are off.
         */
        struct EncodingData
        {
            std::map<SimpleIntegerVariableID, ChannellingData> channelling_constraints{};
            std::map<SimpleIntegerVariableID, ProofOnlySimpleIntegerVariableID> mag_var{};
            std::pair<ProofLine, ProofLine> v3_eq_product_lines{};
            // cake_pb_cp gates the product->|Z| channel on the sign atom [Z>=0]
            // (v3_eq_product_lines: {mag_Zge0_ge, mag_Zge0_le}) and mirrors it on
            // [Z<0] (v3_eq_product_lines_neg: {mag_Zlt0_ge, mag_Zlt0_le}). The
            // product-bound provers pick the row matching Z's sign in each branch
            // (sign(X)*sign(Y)) and discharge the sign atom. The legacy scheme's
            // ungated zprod lines leave z_product_ge0_gated false and _neg empty.
            std::optional<std::pair<ProofLine, ProofLine>> v3_eq_product_lines_neg{};
            bool z_product_ge0_gated = false;
            std::vector<ProofLine> sign_lines{};
            // Consumed at install time to create the persistent constraint
            // state that propagate() mutates through its handle.
            std::vector<std::vector<BitProductData>> initial_bit_products{};
        };

        /**
         * \brief Emit cake_pb_cp's magnitude bit-product encoding of v1 * v2 = v3 into the
         * OPB (the only scheme; it covers signed operands). `link`, when set, disambiguates
         * one multiplication of a chain sharing a constraint id (Power's base^k), folding it
         * into the bit-name index tuples and @c roles so the per-link flags do not clash.
         */
        [[nodiscard]] auto define_encoding(ProofModel & model, const State & initial_state, const ConstraintID & constraint_id,
            const std::string & label_id, SimpleIntegerVariableID v1, SimpleIntegerVariableID v2, SimpleIntegerVariableID v3,
            std::optional<long long> link = std::nullopt) -> EncodingData;

        /**
         * \brief One pass of bounds consistent multiplication filtering for
         * v1 * v2 = v3: product bounds onto v3, then quotient filtering onto
         * v1 and v2. Callers loop to their own fixpoint. The assertion hints
         * carry hints::Multiply{owner}, naming the owning constraint.
         */
        auto propagate(SimpleIntegerVariableID v1, SimpleIntegerVariableID v2, SimpleIntegerVariableID v3, const State & state, auto & inference,
            ProofLogger * const logger, const EncodingData & encoding, ConstraintStateHandle bit_products_handle, const ConstraintID & owner) -> void;
    }

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
