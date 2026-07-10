#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MULTIPLY_SIGNED_MULTIPLY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MULTIPLY_SIGNED_MULTIPLY_HH

#include <gcs/constraint_id.hh>
#include <gcs/constraints/innards/product_encoding.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_model-fwd.hh>
#include <gcs/innards/state.hh>
#include <gcs/variable_id.hh>

#include <optional>
#include <string>
#include <vector>

namespace gcs::innards::signed_multiply
{
    /**
     * \brief Everything one signed multiplication x * y = z carries between
     * its cake encoding and its propagation: the operand handles, their
     * initial bounds (the factor-bound justifications cite the initial-domain
     * rows for the untightened side of a refuted range), and the slot-keyed
     * encoding handles, empty when proofs are off.
     *
     * \ingroup Innards
     */
    struct Data
    {
        IntegerVariableID x = 0_c, y = 0_c, z = 0_c;
        Integer x_init_lo{0}, x_init_hi{0};
        Integer y_init_lo{0}, y_init_hi{0};
        std::optional<product_enc::MagnitudeChannel> chan_x, chan_y;
        product_enc::BitProductGrid grid{};
        std::optional<product_enc::ResultChannel> zchan;
        std::vector<ProofLine> sign_lines{};
    };

    /**
     * \brief Capture the operands and, when there is a model, emit cake's
     * multiplication encoding for x * y = z: two magnitude channels, the
     * bit-product grid, the result channel and the six sign clauses, exactly
     * as cake_pb_cp does. `link` disambiguates one multiplication of a chain
     * sharing a constraint id (Power's base^k).
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto make_data(ProofModel * const optional_model, const State & initial_state, const ConstraintID & constraint_id,
        IntegerVariableID x, IntegerVariableID y, IntegerVariableID z, std::optional<long long> link = std::nullopt) -> Data;

    /**
     * \brief One pass of bounds consistent multiplication filtering for
     * x * y = z: product bounds onto z, then quotient filtering onto x and y.
     * Callers loop to their own fixpoint. Justifications follow the thesis's
     * Chapter 7 procedures over the encoding handles in Data; the assertion
     * hints carry hints::Multiply naming the owning constraint.
     *
     * \ingroup Innards
     */
    auto propagate(Data &, const State &, auto & inference, ProofLogger * const, const ConstraintID & owner) -> void;
}

#endif
