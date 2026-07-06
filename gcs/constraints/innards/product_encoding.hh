#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_PRODUCT_ENCODING_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_PRODUCT_ENCODING_HH

#include <gcs/constraint_id.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_model-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/proofs/pseudo_boolean.hh>
#include <gcs/innards/state.hh>
#include <gcs/variable_id.hh>

#include <optional>
#include <string>
#include <vector>

namespace gcs::innards
{
    struct StringLiteral;
}

namespace gcs::innards::product_enc
{
    /**
     * \brief Naming for one multiplication of a chain that shares a single
     * constraint id (Power's base^k): folds the link index into cake bit-name
     * index tuples, `@c` roles, and product-flag names, so per-link flags do
     * not clash. Every operation is a no-op when link is nullopt (a standalone
     * multiplication), keeping the names byte-identical to cake_pb_cp's.
     *
     * \ingroup Innards
     */
    struct LinkNaming
    {
        std::optional<long long> link{};

        [[nodiscard]] auto role_prefix() const -> std::string
        {
            return link ? "l" + std::to_string(*link) + "_" : std::string{};
        }

        [[nodiscard]] auto bit_indices(std::vector<long long> indices) const -> std::vector<long long>
        {
            if (link)
                indices.insert(indices.begin(), *link);
            return indices;
        }

        [[nodiscard]] auto grid_cell_name(Integer i, Integer j) const -> std::string
        {
            return (link ? std::to_string(*link) + "_" : std::string{}) + std::to_string(i.raw_value) + "_" + std::to_string(j.raw_value);
        }
    };

    /**
     * \brief One operand slot's magnitude channel, cake_pb_cp style: a
     * non-negative magnitude bit-vector pinned to |v| by four half-reified
     * rows gated on the reified sign atom, `[v>=0] => mag = v` and
     * `[v<0] => mag = -v`. The magnitude is a proof-only variable for
     * Multiply and Power, and a state variable (whose bits are registered
     * as cake's encoder-internal bits) for Divide and Modulus.
     *
     * Slot-keyed by design: a repeated operand gets one channel per slot,
     * both over the same v, exactly as cake emits for `(multiply X X Z)`.
     *
     * \ingroup Innards
     */
    struct MagnitudeChannel
    {
        SimpleOrProofOnlyIntegerVariableID mag;
        ProofLine pos_ge;
        ProofLine pos_le;
        ProofLine neg_ge;
        ProofLine neg_le;
    };

    /**
     * \brief Emit a magnitude channel with a fresh proof-only magnitude
     * variable `mult_mag_<letter>` sized from v's initial bounds (Multiply
     * and Power's flavour). axis 0 renders as cake's X bits, 1 as Y.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto emit_magnitude_channel(ProofModel & model, const State & initial_state, const ConstraintID & owner, const std::string & label,
        const StringLiteral & op, IntegerVariableID v, long long axis, const std::string & letter, const LinkNaming & naming) -> MagnitudeChannel;

    /**
     * \brief Emit a magnitude channel for an existing non-negative state
     * variable mag with range [0, mag_bit_max] (Divide and Modulus's flavour:
     * the propagation needs solver-side domains for the magnitude). Registers
     * mag's bits as cake's axis-<axis> encoder-internal bits under mag_name,
     * then channels them to v.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto emit_magnitude_channel(ProofModel & model, const ConstraintID & owner, const std::string & label, const StringLiteral & op,
        SimpleIntegerVariableID v, SimpleIntegerVariableID mag, Integer mag_bit_max, long long axis, const std::string & letter,
        const std::string & mag_name) -> MagnitudeChannel;

    /**
     * \brief One bit-product flag `x[id][i_j][prod] <=> bit_a_i AND bit_b_j`,
     * with the deterministic labels of its two reifying halves ([r] forwards,
     * [f] reverse), and slots for the lazily derived per-cell W-lines that
     * the product upper-bound justification caches (thesis Justification
     * Subprocedure 7.2).
     *
     * \ingroup Innards
     */
    struct BitProductCell
    {
        ProofFlag flag;
        ProofLineLabel forwards_reif;
        ProofLineLabel reverse_reif;
        std::optional<ProofLine> w_a{};
        std::optional<ProofLine> w_b{};
    };

    /**
     * \brief The full bit-product grid for |a| * |b|: the flags, and the
     * weighted sums +/- Sum 2^(i+j) prod_ij that every row mentioning the
     * product magnitude is expressed over.
     *
     * \ingroup Innards
     */
    struct BitProductGrid
    {
        std::vector<std::vector<BitProductCell>> cells;
        WPBSum sum;
        WPBSum neg_sum;
    };

    /**
     * \brief Emit the bit-product grid over two magnitude bit-vectors (proof
     * only or state variables with registered bits).
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto emit_bit_product_grid(ProofModel & model, const ConstraintID & owner, const std::string & label,
        const SimpleOrProofOnlyIntegerVariableID & bits_a, const SimpleOrProofOnlyIntegerVariableID & bits_b, const LinkNaming & naming)
        -> BitProductGrid;

    /**
     * \brief The four rows channelling the grid sum to the signed result:
     * `[Z>=0] => Z = Sum 2^(i+j) prod_ij` (ge0 pair) and
     * `[Z<0] => -Z = Sum 2^(i+j) prod_ij` (lt0 pair), cake's mag_Z rows.
     *
     * \ingroup Innards
     */
    struct ResultChannel
    {
        ProofLine ge0_ge;
        ProofLine ge0_le;
        ProofLine lt0_ge;
        ProofLine lt0_le;
    };

    [[nodiscard]] auto emit_result_channel(ProofModel & model, const std::string & label, const StringLiteral & op, IntegerVariableID v3,
        const BitProductGrid & grid, const LinkNaming & naming) -> ResultChannel;

    /**
     * \brief cake's six sign clauses for v1 * v2 = v3 over the reified atoms:
     * either operand zero, or matching signs, force `[v3>=0]`; strictly
     * opposite signs force `[v3<0]`.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto emit_sign_clauses(ProofModel & model, const std::string & label, const StringLiteral & op, IntegerVariableID v1,
        IntegerVariableID v2, IntegerVariableID v3, const LinkNaming & naming) -> std::vector<ProofLine>;
}

#endif
