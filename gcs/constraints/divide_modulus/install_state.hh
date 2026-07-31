#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DIVIDE_MODULUS_INSTALL_STATE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DIVIDE_MODULUS_INSTALL_STATE_HH

#include <gcs/constraints/innards/tabulation.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <memory>
#include <optional>

namespace gcs::innards::divide_modulus
{
    /**
     * \brief A non-negative magnitude STATE variable equal to |v|, channelled to v
     * by cake's <letter>ge0/<letter>lt0 channel (four half-reified rows
     * @c[id][<letter>{ge0,lt0}_{ge,le}]) and carrying axis-<axis> free magnitude
     * bits x[id][<axis>_*][bin]. mult_bc multiplies these magnitudes, so its
     * operands are always non-negative.
     *
     * The variable and its bit count are allocated by prepare(), so the
     * propagation runs with or without proofs; the four line handles are filled in
     * by define_proof_model(), and stay empty when proofs are off.
     *
     * \ingroup Innards
     */
    struct CakeMagnitude
    {
        SimpleIntegerVariableID var{0};
        Integer num_bits = 0_i;
        std::optional<ProofLine> pos_ge, pos_le, neg_ge, neg_le;
    };

    /// Everything the propagator and its justifications share; defined in divide_modulus.cc.
    struct DefaultProductData;

    /**
     * \brief What prepare() works out for Divide and Modulus, and the other two
     * phases consume.
     *
     * Divide and Modulus are one decomposition with the exposed slot swapped, so
     * all three phases are shared code parameterised on which slot that is; this
     * is what travels between them.
     *
     * \ingroup Innards
     */
    struct InstallState
    {
        /// A structurally constant zero divisor: nothing is allocated, and the other two
        /// phases write the trivially false row and install a contradiction instead.
        bool zero_divisor = false;

        /// The quotient, which is the user's variable for Divide and the auxiliary
        /// magnitude |q| for Modulus.
        IntegerVariableID q = 0_c;

        /// Modulus's quotient magnitude, or Divide's inert remainder slot, with the
        /// bit-implied upper bound the proof registers its bits against.
        SimpleIntegerVariableID aux{0};
        Integer aux_bit_max = 0_i;

        /// The bit-product grid's two non-negative operands. Divide channels both (|q|
        /// and |y|); Modulus channels only the divisor, its quotient magnitude being a
        /// free axis-0 bit-sum, so quotient_mag is unused there.
        CakeMagnitude quotient_mag{}, divisor_mag{};

        std::shared_ptr<DefaultProductData> data;

        /// Unset when the constraint is not tabulating.
        std::optional<TabulationPlan> tabulation;

        /// Modulus's range and remainder-sign rows. They feed stages that must exist
        /// with proofs off too, so the stages are built in install_propagators() from
        /// these handles rather than alongside the rows.
        std::optional<ProofLine> rng_hi, rng_lo, sgn_pos, sgn_neg;
    };
}

#endif
