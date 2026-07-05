#include <gcs/constraints/divide_modulus/divide_modulus.hh>
#include <gcs/constraints/divide_modulus/hints.hh>
#include <gcs/constraints/innards/arithmetic_utils.hh>
#include <gcs/constraints/innards/linear_stages.hh>
#include <gcs/constraints/innards/product_encoding.hh>
#include <gcs/constraints/innards/tabulation.hh>
#include <gcs/constraints/innards/triggers.hh>
#include <gcs/constraints/linear/hints.hh>
#include <gcs/constraints/linear/propagate.hh>
#include <gcs/constraints/linear/utils.hh>
#include <gcs/constraints/multiply/multiply_bc.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/power.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>
#include <gcs/variable_condition.hh>

#include <algorithm>
#include <cstddef>
#include <limits>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_shared;
using std::make_unique;
using std::max;
using std::min;
using std::move;
using std::nullopt;
using std::numeric_limits;
using std::optional;
using std::shared_ptr;
using std::string;
using std::to_string;
using std::unique_ptr;
using std::vector;

namespace
{
    // Is (x, y, q, r) in the truncated-division relation? That is, y is not
    // zero, x / y = q rounding towards zero, and r is the remainder (which
    // therefore takes the sign of x). Everything else in this file is
    // scaffolding to propagate exactly this.
    auto is_in_relation(Integer x, Integer y, Integer q, Integer r) -> bool
    {
        if (y == 0_i)
            return false;
        if (x.raw_value == numeric_limits<long long>::min() && y == -1_i)
            return false;
        return x.raw_value / y.raw_value == q.raw_value && x.raw_value % y.raw_value == r.raw_value;
    }

    // A non-negative magnitude STATE variable equal to |v|, channelled to v by cake's
    // <letter>ge0/<letter>lt0 channel (four half-reified rows @c[id][<letter>{ge0,lt0}_{ge,le}])
    // and carrying axis-<axis> free magnitude bits x[id][<axis>_*][bin]. mult_bc multiplies
    // these magnitudes, so its operands are always non-negative.
    struct CakeMagnitude
    {
        SimpleIntegerVariableID var;
        Integer num_bits;
        optional<ProofLine> pos_ge, pos_le, neg_ge, neg_le;
    };

    // The magnitude STATE variable and its bit count are allocated unconditionally so the
    // propagation runs with or without proofs; the channel rows and bit registration are only
    // emitted when there is a model (proofs on), leaving the channel lines nullopt otherwise.
    auto make_cake_magnitude(ProofModel * const model, State & state, const ConstraintID & owner, const std::string & label, StringLiteral op,
        SimpleIntegerVariableID v, long long axis, const std::string & letter, const std::string & aux_name) -> CakeMagnitude
    {
        auto mag_ub = max(abs(state.lower_bound(v)), abs(state.upper_bound(v)));
        auto bits = 0_i;
        while (power2(bits) <= mag_ub)
            bits += 1_i;
        auto mag = state.allocate_integer_variable_with_state(0_i, power2(bits) - 1_i);
        if (! model)
            return {mag, bits, nullopt, nullopt, nullopt, nullopt};
        auto chan =
            product_enc::emit_magnitude_channel(*model, owner, label, op, v, mag, power2(bits) - 1_i, axis, letter, aux_name + to_string(mag.index));
        return {mag, bits, chan.pos_ge, chan.pos_le, chan.neg_ge, chan.neg_le};
    }

    // The bit-product flags x[id][i_j][prod] = mag_a_i AND mag_b_j and their weighted sum
    // mag_a * mag_b, appended to enc.initial_bit_products. Proof-only: the callers compute the
    // product's declared max w_hi themselves from the magnitudes' bit counts.
    struct CakeBitProducts
    {
        WPBSum product_sum, neg_product;
    };

    auto emit_cake_bit_products(ProofModel & model, const ConstraintID & owner, const std::string & label, SimpleIntegerVariableID mag_a,
        SimpleIntegerVariableID mag_b, mult_bc::EncodingData & enc) -> CakeBitProducts
    {
        auto grid = product_enc::emit_bit_product_grid(model, owner, label, mag_a, mag_b, product_enc::LinkNaming{});
        for (const auto & row : grid.cells) {
            enc.initial_bit_products.emplace_back();
            for (const auto & cell : row)
                enc.initial_bit_products.back().emplace_back(
                    mult_bc::BitProductData{cell.flag, cell.forwards_reif, cell.reverse_reif, nullopt, nullopt});
        }
        return {grid.sum, grid.neg_sum};
    }

    // The four stages pinning mag = |v| in both directions off its cake channel, split on
    // sign(v). pos_threshold gates the non-negative half: 0 when v may be zero (the quotient),
    // 1 when v is known non-zero (the divisor).
    auto append_magnitude_stages(std::vector<LinearStage> & stages, SimpleIntegerVariableID mag, SimpleIntegerVariableID v,
        const CakeMagnitude & chan, Integer pos_threshold) -> void
    {
        auto [t_le, m_le] = tidy_up_linear(WeightedSum{} + 1_i * mag + -1_i * v);
        stages.emplace_back(LinearStage{t_le, 0_i + m_le, false, {chan.pos_ge, nullopt}, optional{v >= pos_threshold}});
        auto [t_ge, m_ge] = tidy_up_linear(WeightedSum{} + -1_i * mag + 1_i * v);
        stages.emplace_back(LinearStage{t_ge, 0_i + m_ge, false, {chan.pos_le, nullopt}, optional{v >= pos_threshold}});
        auto [t_nle, m_nle] = tidy_up_linear(WeightedSum{} + 1_i * mag + 1_i * v);
        stages.emplace_back(LinearStage{t_nle, 0_i + m_nle, false, {chan.neg_le, nullopt}, optional{v < 0_i}});
        auto [t_nge, m_nge] = tidy_up_linear(WeightedSum{} + -1_i * mag + -1_i * v);
        stages.emplace_back(LinearStage{t_nge, 0_i + m_nge, false, {chan.neg_ge, nullopt}, optional{v < 0_i}});
    }

    // The shared decomposition: x = q * y + r, |r| < |y|, sign(r) = sign(x)
    // (or r = 0), all emitted as one flat @c[id][role] OPB block and run by
    // one propagator (issue #448). Divide exposes q and creates r as an
    // auxiliary; Modulus the other way around. A constant divisor (or, for
    // Divide, a constant quotient) makes the product a linear term, so there
    // is no multiplication at all; otherwise the product goes through the
    // exposed mult_bc machinery on plain variables, with any views channelled
    // through plain copies first -- once the user's variables are fixed, the
    // multiplication must pin the unbranched auxiliary (or fail) by
    // propagation alone, and mult_bc's quotient filtering does exactly that
    // for plain arguments.
    template <typename Hint_>
    auto install_divide_modulus(const ConstraintID & owner, bool expose_quotient, const IntegerVariableID & x, const IntegerVariableID & y,
        const IntegerVariableID & out, const std::variant<consistency::Auto, consistency::BC, consistency::Tabulated> & level,
        Propagators & propagators, State & initial_state, ProofModel * const optional_model) -> void
    {
        auto ax = affine_of(x), ay = affine_of(y), aout = affine_of(out);

        auto [xlo, xhi] = initial_state.bounds(x);
        auto [ylo, yhi] = initial_state.bounds(y);

        // A structurally constant zero divisor makes the whole constraint
        // unsatisfiable, relationally rather than as an error.
        if ((! ay.var) && ay.offset == 0_i) {
            if (optional_model) {
                // (StringLiteral wants an actual literal, hence the branch)
                if (expose_quotient)
                    optional_model->add_constraint("Divide", "division by constant zero", WPBSum{} >= 1_i);
                else
                    optional_model->add_constraint("Modulus", "division by constant zero", WPBSum{} >= 1_i);
            }
            propagators.install_initial_contradiction("division by constant zero", JustifyUsingRUP{Hint_{owner}});
            return;
        }

        // Biggest possible |y| bounds the remainder: |r| <= max|y| - 1.
        auto may = max(ylo < 0_i ? -ylo : ylo, yhi < 0_i ? -yhi : yhi);
        auto rmax = max(0_i, may - 1_i);

        // The quotient can be no bigger in magnitude than the dividend (as
        // |y| >= 1 whenever the relation holds at all), and when the divisor
        // has a fixed sign, truncated division is monotone enough that the
        // box corners bound it.
        auto mx = max(xlo < 0_i ? -xlo : xlo, xhi < 0_i ? -xhi : xhi);
        auto q_lo = -mx, q_hi = mx;
        if (ylo > 0_i || yhi < 0_i) {
            q_lo = min({xlo / ylo, xlo / yhi, xhi / ylo, xhi / yhi});
            q_hi = max({xlo / ylo, xlo / yhi, xhi / ylo, xhi / yhi});
        }

        // The default divide/modulus route emits cake_pb_cp's encoding: the product |q|*|y|
        // lives only in bit-product flags feeding the remainder/identity rows, with no w (and,
        // for divide, no r) in the OPB. Plain variable operands take this route (introducing the
        // internal handles inside the proof); views and constant operands fall back to the
        // legacy two's-complement path below. The route is chosen on operand SHAPE alone, so the
        // propagation is the same with or without proofs -- only the proof emission is guarded.
        // Both directions multiply the two NON-NEGATIVE magnitudes |q| and |y| into w = |q||y|
        // (mult_bc with no signed reasoning), split the identity/remainder on sign(x), and
        // recover signed values in the tabulation -- a single magnitude machinery covering
        // every sign of both operands.
        //
        // Divide (default_divide): the exposed slot is q. magq = |q| (a state var
        // channelled to q by cake's Zge0/Zlt0 channel) and absy = |y| (channelled by
        // Yge0/Ylt0) are the mult operands; cake's rem_* rows range 0 <= x - w < |y| over
        // w and x directly (rem_pos gated [x>=0], rem_neg gated [x<0]), so no remainder is
        // materialised at all. The magnitude product carries no mult_bc sign_lines, so the
        // exposed quotient's sign is pinned off the five sgn_* clauses by RUP in the
        // propagator. The tabulation enumerates only x, y, q; a rejected leaf pins
        // magq/absy/w by unit propagation from the assigned q, y and the rem rows refute it.
        //
        // Modulus (default_modulus): the exposed slot is r, and cake leaves the quotient's
        // magnitude a FREE axis-0 bit-sum with no i[Q] channel (no Zge0/Zlt0, no sgn_*). The
        // aux is the quotient magnitude |q|; absy = |y| is the second mult operand. cake
        // splits the identity r = x -/+ |q||y| on sign(x), the range/sign rows bound r, and
        // the tabulation recovers the signed quotient sign(x)sign(y)|q|.
        bool plain_operands = ax.coeff == 1_i && ax.offset == 0_i && ay.var && ay.coeff == 1_i && ay.offset == 0_i && aout.var && aout.coeff == 1_i &&
            aout.offset == 0_i;
        bool default_divide = expose_quotient && plain_operands;
        bool default_modulus = (! expose_quotient) && plain_operands;

        // The exposed slot is the user's; the other is an auxiliary, with
        // bounds tightened by the sign-of-dividend rule where easy.
        IntegerVariableID q = 0_c, r = 0_c;
        SimpleIntegerVariableID aux = SimpleIntegerVariableID{0};
        if (expose_quotient && default_divide) {
            q = out;
            // The default divide path materialises no remainder (neither in the OPB nor in the
            // proof): cake's rem_* rows range x - w directly, so the aux is an inert state
            // slot, never introduced, enumerated, or meaningfully watched.
            aux = initial_state.allocate_integer_variable_with_state(0_i, 0_i);
            r = aux;
        }
        else if (expose_quotient) {
            // Legacy divide (views / constant operands): the remainder is a signed auxiliary
            // in the OPB, pinned by the w + r = x identity.
            q = out;
            auto r_lo = xlo >= 0_i ? 0_i : -rmax;
            auto r_hi = xhi <= 0_i ? 0_i : rmax;
            aux = initial_state.allocate_integer_variable_with_state(r_lo, r_hi);
            if (optional_model)
                optional_model->set_up_integer_variable(aux, r_lo, r_hi, "aux_divide_remainder" + to_string(aux.index), nullopt);
            r = aux;
        }
        else if (default_modulus) {
            r = out;
            // The aux is the quotient MAGNITUDE |q|, a free axis-0 bit-sum sized by the
            // dividend's magnitude (|q| <= |x| since |y| >= 1). Its provable range is the
            // bit-implied [0, 2^n - 1]; give the state that range (like divide's product w)
            // and register its bits in cake's x[id][0_*][bin] naming with no OPB bounds, so
            // they ARE the magnitude the bit products multiply. The signed quotient is never
            // materialised: the propagation is in magnitude space and the tabulation recovers
            // sign(x)sign(y)|q| for its relation check.
            auto q_bits = 0_i;
            while (power2(q_bits) <= mx)
                q_bits += 1_i;
            auto q_bit_max = power2(q_bits) - 1_i;
            aux = initial_state.allocate_integer_variable_with_state(0_i, q_bit_max);
            if (optional_model)
                optional_model->register_state_variable_bits_in_proof(
                    aux, 0_i, q_bit_max, "aux_modulus_quotient" + to_string(aux.index), CakeBitNaming{owner, {0}, "bin", nullopt, false, true});
            q = aux;
        }
        else {
            r = out;
            aux = initial_state.allocate_integer_variable_with_state(q_lo, q_hi);
            if (optional_model)
                optional_model->set_up_integer_variable(aux, q_lo, q_hi, "aux_modulus_quotient" + to_string(aux.index), nullopt);
            q = aux;
        }
        auto aq = affine_of(q);

        auto label = as_string(owner);

        vector<LinearStage> legacy_stages;
        auto add_equality = [&](const WeightedSum & sum, Integer value, const string & role) {
            add_equality_stage(legacy_stages, optional_model, label, sum, value, role);
        };
        auto add_le = [&](const WeightedSum & sum, Integer value, const string & role, const optional<IntegerVariableCondition> & gate) {
            add_le_stage(legacy_stages, optional_model, label, sum, value, role, gate);
        };

        // x = q * y + r. With a constant divisor or a constant quotient the
        // product is a linear term; otherwise, define w = x - r (pinned by
        // propagation whenever x and r are known) and multiply directly into
        // it: q * y = w, on plain variables.
        bool needs_mult = ay.var && aq.var;
        mult_bc::EncodingData legacy_encoding;
        optional<ConstraintStateHandle> bit_products_handle;
        SimpleIntegerVariableID mult_q = aux, mult_y = aux, mult_w = aux; // overwritten when needs_mult
        shared_ptr<mult_bc::EncodingData> default_encoding;
        shared_ptr<vector<LinearStage>> default_stages;

        if (default_divide) {
            // Divide, any sign of the dividend. BOTH the x >= 0 and x < 0 remainder rows
            // and w-stages are live, each gated on sign(x) so only the matching regime fires
            // once x is branched. The quotient's sign is pinned off the sgn_* clauses (for
            // whichever signs of x and y are established). No remainder is materialised: cake's
            // rem_* rows range x - w directly, so there is no |r| aux to introduce (which would
            // need a proof-only |x|); the tabulation enumerates only x, y, q.
            auto q_eff = *aq.var, y_eff = *ay.var, x_eff = *ax.var;

            default_encoding = make_shared<mult_bc::EncodingData>();
            auto & enc = *default_encoding;
            enc.z_product_ge0_gated = false;

            // magq = |q| (Z channel to the exposed quotient) and absy = |y| (Y channel to the
            // divisor) are the two non-negative mult_bc operands; w = magq * absy. The magnitude
            // state vars and the product's declared max are set regardless of proofs.
            auto zchan = make_cake_magnitude(optional_model, initial_state, owner, label, "Divide", q_eff, 0, "Z", "aux_divide_qmag");
            auto ychan = make_cake_magnitude(optional_model, initial_state, owner, label, "Divide", y_eff, 1, "Y", "aux_divide_absdivisor");
            auto magq = zchan.var, absy = ychan.var;
            auto w_hi = (power2(zchan.num_bits) - 1_i) * (power2(ychan.num_bits) - 1_i);

            auto w = initial_state.allocate_integer_variable_with_state(0_i, w_hi);
            mult_q = magq, mult_y = absy, mult_w = w;

            // Stages: magq (0-3) and absy (4-7) channels, then the x >= 0 w-stages (8 = wlo,
            // 9/10 = whi split on sign(y)) and the x < 0 w-stages (11 = wlo, 12/13 = whi). Built
            // regardless of proofs; the w-stage lines fuse the rem row with w = product in the
            // initialiser (proofs on only), and the channel lines are nullopt proofs-off.
            default_stages = make_shared<vector<LinearStage>>();
            append_magnitude_stages(*default_stages, magq, q_eff, zchan, 0_i);
            append_magnitude_stages(*default_stages, absy, y_eff, ychan, 1_i);
            auto [t_wlo_p, m_wlo_p] = tidy_up_linear(WeightedSum{} + 1_i * w + -1_i * x_eff);
            default_stages->emplace_back(LinearStage{t_wlo_p, 0_i + m_wlo_p, false, {nullopt, nullopt}, optional{x_eff >= 0_i}});
            auto [t_whip_p, m_whip_p] = tidy_up_linear(WeightedSum{} + 1_i * x_eff + -1_i * w + -1_i * y_eff);
            default_stages->emplace_back(LinearStage{t_whip_p, -1_i + m_whip_p, false, {nullopt, nullopt}, optional{y_eff >= 1_i}});
            auto [t_whin_p, m_whin_p] = tidy_up_linear(WeightedSum{} + 1_i * x_eff + -1_i * w + 1_i * y_eff);
            default_stages->emplace_back(LinearStage{t_whin_p, -1_i + m_whin_p, false, {nullopt, nullopt}, optional{y_eff < 0_i}});
            auto [t_wlo_n, m_wlo_n] = tidy_up_linear(WeightedSum{} + 1_i * w + 1_i * x_eff);
            default_stages->emplace_back(LinearStage{t_wlo_n, 0_i + m_wlo_n, false, {nullopt, nullopt}, optional{x_eff < 1_i}});
            auto [t_whip_n, m_whip_n] = tidy_up_linear(WeightedSum{} + -1_i * x_eff + -1_i * w + -1_i * y_eff);
            default_stages->emplace_back(LinearStage{t_whip_n, -1_i + m_whip_n, false, {nullopt, nullopt}, optional{y_eff >= 1_i}});
            auto [t_whin_n, m_whin_n] = tidy_up_linear(WeightedSum{} + -1_i * x_eff + -1_i * w + 1_i * y_eff);
            default_stages->emplace_back(LinearStage{t_whin_n, -1_i + m_whin_n, false, {nullopt, nullopt}, optional{y_eff < 0_i}});

            if (optional_model) {
                auto [product_sum, neg_product] = emit_cake_bit_products(*optional_model, owner, label, magq, absy, enc);

                // Both remainder-row sets: 0 <= x - |q||y| < |y| (rem_pos, gated [x>=0]) and
                // 0 <= -x - |q||y| < |y| (rem_neg, gated [x<1]).
                auto xge0 = HalfReifyOnConjunctionOf{x_eff >= 0_i};
                auto xlt0 = HalfReifyOnConjunctionOf{x_eff < 1_i};
                auto rem_pos_lo =
                    optional_model->add_labelled_constraint(label, "rem_pos_lo", "Divide", "remainder", neg_product + 1_i * x_eff >= 0_i, xge0);
                auto rem_pos_hi = optional_model->add_labelled_constraint(
                    label, "rem_pos_hi", "Divide", "remainder", product_sum + -1_i * x_eff + 1_i * absy >= 1_i, xge0);
                auto rem_neg_hi =
                    optional_model->add_labelled_constraint(label, "rem_neg_hi", "Divide", "remainder", neg_product + -1_i * x_eff >= 0_i, xlt0);
                auto rem_neg_lo = optional_model->add_labelled_constraint(
                    label, "rem_neg_lo", "Divide", "remainder", product_sum + 1_i * x_eff + 1_i * absy >= 1_i, xlt0);

                optional_model->add_labelled_constraint(
                    label, "sgn_pp", "Divide", "sign", WPBSum{} + 1_i * (x < 1_i) + 1_i * (y < 1_i) + 1_i * (q >= 0_i) >= 1_i);
                optional_model->add_labelled_constraint(
                    label, "sgn_nn", "Divide", "sign", WPBSum{} + 1_i * (x >= 0_i) + 1_i * (y >= 0_i) + 1_i * (q >= 0_i) >= 1_i);
                optional_model->add_labelled_constraint(
                    label, "sgn_pn", "Divide", "sign", WPBSum{} + 1_i * (x < 1_i) + 1_i * (y >= 0_i) + 1_i * (q < 1_i) >= 1_i);
                optional_model->add_labelled_constraint(
                    label, "sgn_np", "Divide", "sign", WPBSum{} + 1_i * (x >= 0_i) + 1_i * (y < 1_i) + 1_i * (q < 1_i) >= 1_i);
                optional_model->add_labelled_constraint(label, "sgn_x0", "Divide", "sign", WPBSum{} + 1_i * (x != 0_i) + 1_i * (q < 1_i) >= 1_i);
                optional_model->add_labelled_constraint(
                    label, "nonzero", "Divide", "divisor is not zero", WPBSum{} + 1_i * (y >= 1_i) + 1_i * (y < 0_i) >= 1_i);

                optional_model->register_state_variable_bits_in_proof(w, 0_i, w_hi, "aux_divide_product" + to_string(w.index));

                propagators.install_initialiser(
                    [enc = default_encoding, stg = default_stages, product_sum, w, rem_pos_lo, rem_pos_hi, rem_neg_hi, rem_neg_lo,
                        y_pos_ge = *ychan.pos_ge, y_neg_le = *ychan.neg_le](State &, auto &, ProofLogger * const logger) -> void {
                        if (! logger || logger->get_assertion_level() > AssertionLevel::Off)
                            return;
                        enc->v3_eq_product_lines = logger->introduce_bits_of(product_sum, w, ProofLevel::Top);
                        // x >= 0 w-stages.
                        PolBuilder pb_wlo_p;
                        pb_wlo_p.add(rem_pos_lo).add(enc->v3_eq_product_lines.second);
                        (*stg)[8].lines = {pb_wlo_p.emit(*logger, ProofLevel::Top), nullopt};
                        PolBuilder pb_whip_p;
                        pb_whip_p.add(rem_pos_hi).add(enc->v3_eq_product_lines.first).add(y_pos_ge);
                        (*stg)[9].lines = {pb_whip_p.emit(*logger, ProofLevel::Top), nullopt};
                        PolBuilder pb_whin_p;
                        pb_whin_p.add(rem_pos_hi).add(enc->v3_eq_product_lines.first).add(y_neg_le);
                        (*stg)[10].lines = {pb_whin_p.emit(*logger, ProofLevel::Top), nullopt};
                        // x < 0 w-stages.
                        PolBuilder pb_wlo_n;
                        pb_wlo_n.add(rem_neg_hi).add(enc->v3_eq_product_lines.second);
                        (*stg)[11].lines = {pb_wlo_n.emit(*logger, ProofLevel::Top), nullopt};
                        PolBuilder pb_whip_n;
                        pb_whip_n.add(rem_neg_lo).add(enc->v3_eq_product_lines.first).add(y_pos_ge);
                        (*stg)[12].lines = {pb_whip_n.emit(*logger, ProofLevel::Top), nullopt};
                        PolBuilder pb_whin_n;
                        pb_whin_n.add(rem_neg_lo).add(enc->v3_eq_product_lines.first).add(y_neg_le);
                        (*stg)[13].lines = {pb_whin_n.emit(*logger, ProofLevel::Top), nullopt};
                    });
            }

            bit_products_handle = initial_state.add_persistent_constraint_state(enc.initial_bit_products);
        }
        else if (default_modulus) {
            // The default modulus path: the exposed slot is r; the quotient magnitude |q| (the
            // aux, axis-0 free magnitude) and the divisor magnitude |y| (absy, axis-1 free
            // magnitude, pinned to |y| by cake's Yge0/Ylt0 channel) multiply to w = |q||y|.
            // The identity splits on sign(x): r = x - w off id_pos_* (gated [x>=0]) and
            // r = x + w off id_neg_* (gated [x<0], since q*y = -w for x < 0); the range/sign
            // rows bound 0 <= r < |y| = absy (x>=0) or -|y| < r <= 0 (x<0). Both mult operands
            // are non-negative, so mult_bc needs no signed reasoning and its quotient filtering
            // divides w by the non-negative absy (dividing by the signed y would infer a
            // wrong-signed |q|). Every plain-operand modulus, any sign of x and y, takes this.
            //
            // r and the operands are the plain underlying *aout.var / *a*.var, not view
            // wrappers: the identity stage propagates the exposed r off the wide product w,
            // and deviewing that defeats the reverse unit propagation.
            auto q_eff = *aq.var, y_eff = *ay.var, x_eff = *ax.var, r_eff = *aout.var;

            default_encoding = make_shared<mult_bc::EncodingData>();
            auto & enc = *default_encoding;
            enc.z_product_ge0_gated = false;

            // absy = |y| (Y channel to the divisor) is mult_bc's divisor operand; the quotient
            // magnitude q_eff is the free axis-0 aux (no Z channel -- cake leaves it free), so
            // w = q_eff * absy over their own bits. The magnitude state var, the product's
            // declared max (q's bit-max times absy's) and w are set regardless of proofs.
            auto ychan = make_cake_magnitude(optional_model, initial_state, owner, label, "Modulus", y_eff, 1, "Y", "aux_modulus_absdivisor");
            auto absy = ychan.var;
            auto w_hi = initial_state.upper_bound(q_eff) * (power2(ychan.num_bits) - 1_i);

            auto w = initial_state.allocate_integer_variable_with_state(0_i, w_hi);
            mult_q = q_eff, mult_y = absy, mult_w = w;

            // The range/sign OPB lines feed their stages below; they exist only proofs-on, so
            // the stages carry nullopt lines (and filter on their terms) proofs-off.
            optional<ProofLine> rng_hi, rng_lo, sgn_pos, sgn_neg;
            default_stages = make_shared<vector<LinearStage>>();

            if (optional_model) {
                auto [product_sum, neg_product] = emit_cake_bit_products(*optional_model, owner, label, q_eff, absy, enc);

                optional_model->add_labelled_constraint(
                    label, "nonzero", "Modulus", "divisor is not zero", WPBSum{} + 1_i * (y >= 1_i) + 1_i * (y < 0_i) >= 1_i);

                // r = x - |q||y|, split on sign(x): id_pos_* (gated [x>=0], r = x - w) and
                // id_neg_* (gated [x<0], r = x + w -- since for x < 0 the quotient product q*y
                // has sign(x), i.e. q*y = -w).
                auto xge0 = HalfReifyOnConjunctionOf{x_eff >= 0_i};
                auto xlt0 = HalfReifyOnConjunctionOf{x_eff < 1_i};
                auto id_pos_ge = optional_model->add_labelled_constraint(
                    label, "id_pos_ge", "Modulus", "identity", neg_product + 1_i * x_eff + -1_i * r_eff >= 0_i, xge0);
                auto id_pos_le = optional_model->add_labelled_constraint(
                    label, "id_pos_le", "Modulus", "identity", product_sum + -1_i * x_eff + 1_i * r_eff >= 0_i, xge0);
                auto id_neg_ge = optional_model->add_labelled_constraint(
                    label, "id_neg_ge", "Modulus", "identity", neg_product + -1_i * x_eff + 1_i * r_eff >= 0_i, xlt0);
                auto id_neg_le = optional_model->add_labelled_constraint(
                    label, "id_neg_le", "Modulus", "identity", product_sum + 1_i * x_eff + -1_i * r_eff >= 0_i, xlt0);

                // |r| < |y| = absy: rng_hi (r < absy) and rng_lo (r > -absy), plus the r-sign
                // rows (r takes x's sign; sgn_pos gated [x>=0], sgn_neg gated [x<0]).
                rng_hi = optional_model->add_labelled_constraint(label, "rng_hi", "Modulus", "range", WPBSum{} + -1_i * r_eff + 1_i * absy >= 1_i);
                rng_lo = optional_model->add_labelled_constraint(label, "rng_lo", "Modulus", "range", WPBSum{} + 1_i * r_eff + 1_i * absy >= 1_i);
                sgn_pos = optional_model->add_labelled_constraint(label, "sgn_pos", "Modulus", "sign", WPBSum{} + 1_i * r_eff >= 0_i, xge0);
                sgn_neg = optional_model->add_labelled_constraint(label, "sgn_neg", "Modulus", "sign", WPBSum{} + -1_i * r_eff >= 0_i, xlt0);

                // w = |q||y| is the product state variable driving mult_bc; its bits are
                // introduced in the proof.
                optional_model->register_state_variable_bits_in_proof(w, 0_i, w_hi, "aux_modulus_product" + to_string(w.index));

                propagators.install_initialiser([enc = default_encoding, stg = default_stages, product_sum, w, id_pos_ge, id_pos_le, id_neg_ge,
                                                    id_neg_le](State &, auto &, ProofLogger * const logger) -> void {
                    if (! logger || logger->get_assertion_level() > AssertionLevel::Off)
                        return;
                    // w = |q||y|; v3_eq_product_lines = {w >= product, w <= product}.
                    enc->v3_eq_product_lines = logger->introduce_bits_of(product_sum, w, ProofLevel::Top);
                    // x >= 0: r >= x - w (id_pos_le + w >= product); r <= x - w (id_pos_ge + w <= product).
                    PolBuilder pb_idle;
                    pb_idle.add(id_pos_le).add(enc->v3_eq_product_lines.first);
                    (*stg)[0].lines = {pb_idle.emit(*logger, ProofLevel::Top), nullopt};
                    PolBuilder pb_idge;
                    pb_idge.add(id_pos_ge).add(enc->v3_eq_product_lines.second);
                    (*stg)[1].lines = {pb_idge.emit(*logger, ProofLevel::Top), nullopt};
                    // x < 0: r >= x + w (id_neg_ge + w <= product); r <= x + w (id_neg_le + w >= product).
                    PolBuilder pb_idle_n;
                    pb_idle_n.add(id_neg_ge).add(enc->v3_eq_product_lines.second);
                    (*stg)[2].lines = {pb_idle_n.emit(*logger, ProofLevel::Top), nullopt};
                    PolBuilder pb_idge_n;
                    pb_idge_n.add(id_neg_le).add(enc->v3_eq_product_lines.first);
                    (*stg)[3].lines = {pb_idge_n.emit(*logger, ProofLevel::Top), nullopt};
                });
            }

            // Stages (built regardless of proofs). The identity, split on sign(x): r = x - w
            // gated [x>=0] (idle/idge off id_pos_*) and r = x + w gated [x<0] (idle_neg/idge_neg
            // off id_neg_*), lines filled in the initialiser once w = product is introduced. The
            // range 0 <= r < absy (x>=0) / -absy < r <= 0 (x<0): rng_hi (r < absy) and rng_lo
            // (r > -absy), both ungated (valid for either sign), plus the r-sign stages sgn_pos
            // (r >= 0 gated [x>=0]) / sgn_neg (r <= 0 gated [x<0]). And absy = |y| off the
            // Yge0/Ylt0 channel, split on sign(y). Only the identity stages need the initialiser;
            // the rest cite an OPB row directly (nullopt proofs-off).
            auto [t_idle, m_idle] = tidy_up_linear(WeightedSum{} + 1_i * x_eff + -1_i * w + -1_i * r_eff);
            default_stages->emplace_back(LinearStage{t_idle, 0_i + m_idle, false, {nullopt, nullopt}, optional{x_eff >= 0_i}});
            auto [t_idge, m_idge] = tidy_up_linear(WeightedSum{} + -1_i * x_eff + 1_i * w + 1_i * r_eff);
            default_stages->emplace_back(LinearStage{t_idge, 0_i + m_idge, false, {nullopt, nullopt}, optional{x_eff >= 0_i}});
            auto [t_idle_n, m_idle_n] = tidy_up_linear(WeightedSum{} + 1_i * x_eff + 1_i * w + -1_i * r_eff);
            default_stages->emplace_back(LinearStage{t_idle_n, 0_i + m_idle_n, false, {nullopt, nullopt}, optional{x_eff < 1_i}});
            auto [t_idge_n, m_idge_n] = tidy_up_linear(WeightedSum{} + -1_i * x_eff + -1_i * w + 1_i * r_eff);
            default_stages->emplace_back(LinearStage{t_idge_n, 0_i + m_idge_n, false, {nullopt, nullopt}, optional{x_eff < 1_i}});
            auto [t_rhi, m_rhi] = tidy_up_linear(WeightedSum{} + 1_i * r_eff + -1_i * absy);
            default_stages->emplace_back(LinearStage{t_rhi, -1_i + m_rhi, false, {rng_hi, nullopt}, nullopt});
            auto [t_rlo, m_rlo] = tidy_up_linear(WeightedSum{} + -1_i * r_eff + -1_i * absy);
            default_stages->emplace_back(LinearStage{t_rlo, -1_i + m_rlo, false, {rng_lo, nullopt}, nullopt});
            auto [t_slo, m_slo] = tidy_up_linear(WeightedSum{} + -1_i * r_eff);
            default_stages->emplace_back(LinearStage{t_slo, 0_i + m_slo, false, {sgn_pos, nullopt}, optional{x_eff >= 0_i}});
            auto [t_shi, m_shi] = tidy_up_linear(WeightedSum{} + 1_i * r_eff);
            default_stages->emplace_back(LinearStage{t_shi, 0_i + m_shi, false, {sgn_neg, nullopt}, optional{x_eff < 1_i}});
            // absy = |y| off the Y channel, split on sign(y).
            append_magnitude_stages(*default_stages, absy, y_eff, ychan, 1_i);

            bit_products_handle = initial_state.add_persistent_constraint_state(enc.initial_bit_products);
        }

        if (! plain_operands && ! needs_mult) {
            // one of d * q + r - x = 0 (constant divisor) or c * y + r - x = 0
            // (Divide with a constant quotient)
            if (! ay.var)
                add_equality(WeightedSum{} + ay.offset * q + 1_i * r + -1_i * x, 0_i, "sum");
            else
                add_equality(WeightedSum{} + aq.offset * y + 1_i * r + -1_i * x, 0_i, "sum");
        }
        else if (! plain_operands) {
            auto y_eff = *ay.var;
            if (ay.coeff != 1_i || ay.offset != 0_i) {
                auto y_plain = initial_state.allocate_integer_variable_with_state(min(ylo, yhi), max(ylo, yhi));
                if (optional_model)
                    optional_model->set_up_integer_variable(y_plain, min(ylo, yhi), max(ylo, yhi),
                        (expose_quotient ? "aux_divide_divisor" : "aux_modulus_divisor") + to_string(y_plain.index), nullopt);
                add_equality(WeightedSum{} + 1_i * y_plain + -1_i * y, 0_i, "divisor");
                y_eff = y_plain;
            }

            auto q_eff = *aq.var;
            if (aq.coeff != 1_i || aq.offset != 0_i) {
                auto [qelo, qehi] = initial_state.bounds(q);
                auto q_plain = initial_state.allocate_integer_variable_with_state(qelo, qehi);
                if (optional_model)
                    optional_model->set_up_integer_variable(q_plain, qelo, qehi, "aux_divide_quotient" + to_string(q_plain.index), nullopt);
                add_equality(WeightedSum{} + 1_i * q_plain + -1_i * q, 0_i, "quotient");
                q_eff = q_plain;
            }

            // w = x - r bounds w from x's and r's ranges, which stay
            // representable however big the dividend is; the q * y corner
            // products can overflow at install time (and are usually looser,
            // the sum of two ranges rather than their product).
            auto [rblo, rbhi] = initial_state.bounds(r);
            auto w_lo = xlo - rbhi;
            auto w_hi = xhi - rblo;
            auto w = initial_state.allocate_integer_variable_with_state(w_lo, w_hi);
            if (optional_model)
                optional_model->set_up_integer_variable(
                    w, w_lo, w_hi, (expose_quotient ? "aux_divide_product" : "aux_modulus_product") + to_string(w.index), nullopt);

            if (optional_model)
                legacy_encoding = mult_bc::define_encoding(*optional_model, initial_state, owner, label, q_eff, y_eff, w);
            bit_products_handle = initial_state.add_persistent_constraint_state(legacy_encoding.initial_bit_products);
            mult_q = q_eff;
            mult_y = y_eff;
            mult_w = w;

            add_equality(WeightedSum{} + 1_i * w + 1_i * r + -1_i * x, 0_i, "sum");
        }

        // |r| < |y|, plus y != 0, which is where the relational division-by-
        // zero semantics comes from. With a constant divisor the remainder
        // slot's range suffices: it is baked into the auxiliary's bounds for
        // Divide, and posted on the user's remainder for Modulus. With a
        // variable divisor, split on the divisor's sign.
        if (! plain_operands) {
            if (! ay.var) {
                if (! expose_quotient) {
                    add_le(WeightedSum{} + 1_i * r, rmax, "remhi", nullopt);
                    add_le(WeightedSum{} + -1_i * r, rmax, "remlo", nullopt);
                }
            }
            else {
                if (optional_model)
                    optional_model->add_labelled_constraint(
                        label, "nonzero", "DivideModulus", "divisor is not zero", WPBSum{} + 1_i * (y >= 1_i) + 1_i * (y < 0_i) >= 1_i);

                // y >= 1 -> r <= y - 1 and r >= -y + 1
                add_le(WeightedSum{} + 1_i * r + -1_i * y, -1_i, "rangeposhi", y >= 1_i);
                add_le(WeightedSum{} + -1_i * r + -1_i * y, -1_i, "rangeposlo", y >= 1_i);
                // y <= -1 -> r <= -y - 1 and r >= y + 1
                add_le(WeightedSum{} + 1_i * r + 1_i * y, -1_i, "rangeneghi", y < 0_i);
                add_le(WeightedSum{} + -1_i * r + 1_i * y, -1_i, "rangeneglo", y < 0_i);
            }

            // The remainder takes the sign of the dividend, which is what pins
            // truncation: without it, the identity and |r| < |y| admit both the
            // truncated and the floored (quotient, remainder) pair when the signs
            // differ.
            if (ax.var) {
                add_le(WeightedSum{} + -1_i * r, 0_i, "signpos", x >= 0_i);
                add_le(WeightedSum{} + 1_i * r, 0_i, "signneg", x < 1_i);
            }
            else {
                if (ax.offset >= 0_i)
                    add_le(WeightedSum{} + -1_i * r, 0_i, "signpos", nullopt);
                if (ax.offset <= 0_i)
                    add_le(WeightedSum{} + 1_i * r, 0_i, "signneg", nullopt);
            }
        }

        Triggers triggers;
        vector<IntegerVariableID> watched;
        auto watch = [&](const IntegerVariableID & v) {
            if (! holds_alternative<ConstantIntegerVariableID>(v) && std::find(watched.begin(), watched.end(), v) == watched.end())
                watched.push_back(v);
        };
        watch(x);
        watch(y);
        watch(out);
        watch(aux);
        if (needs_mult) {
            watch(mult_q);
            watch(mult_y);
            watch(mult_w);
        }
        triggers.on_bounds = watched;

        bool prune_zero = ay.var != nullopt;
        if (plain_operands) {
            propagators.install(
                owner,
                [enc = default_encoding, stg = default_stages, bph = *bit_products_handle, mult_q = mult_q, mult_y = mult_y, mult_w = mult_w, y = y,
                    q = q, x = x, pin_q_sign = default_divide,
                    owner = owner](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                    do {
                        if (state.in_domain(y, 0_i))
                            inference.infer(logger, y != 0_i, JustifyUsingRUP{Hint_{owner}}, ExplicitReason{ReasonLiterals{}});

                        if (pin_q_sign) {
                            // The magnitude product carries no mult_bc sign_lines, so the exposed
                            // quotient's sign is pinned off the sgn_* clauses by RUP once the signs
                            // of x and y are both established. sgn_pp: x>0 & y>0 -> q>=0; sgn_pn:
                            // x>0 & y<0 -> q<=0; sgn_nn: x<0 & y<0 -> q>=0; sgn_np: x<0 & y>0 ->
                            // q<=0. (On the fixed-negative path only the x<0 rows ever fire.)
                            if (state.lower_bound(x) >= 1_i) {
                                if (state.lower_bound(y) >= 1_i && state.lower_bound(q) < 0_i)
                                    inference.infer(
                                        logger, q >= 0_i, JustifyUsingRUP{Hint_{owner}}, ExplicitReason{ReasonLiterals{x >= 1_i, y >= 1_i}});
                                else if (state.upper_bound(y) < 0_i && state.upper_bound(q) > 0_i)
                                    inference.infer(
                                        logger, q < 1_i, JustifyUsingRUP{Hint_{owner}}, ExplicitReason{ReasonLiterals{x >= 1_i, y < 0_i}});
                            }
                            else if (state.upper_bound(x) < 0_i) {
                                if (state.upper_bound(y) < 0_i && state.lower_bound(q) < 0_i)
                                    inference.infer(
                                        logger, q >= 0_i, JustifyUsingRUP{Hint_{owner}}, ExplicitReason{ReasonLiterals{x < 0_i, y < 0_i}});
                                else if (state.lower_bound(y) >= 1_i && state.upper_bound(q) > 0_i)
                                    inference.infer(
                                        logger, q < 1_i, JustifyUsingRUP{Hint_{owner}}, ExplicitReason{ReasonLiterals{x < 0_i, y >= 1_i}});
                            }
                        }

                        if (! propagate_stages(*stg, state, inference, logger, owner))
                            return PropagatorState::Enable;

                        mult_bc::propagate(mult_q, mult_y, mult_w, state, inference, logger, *enc, bph, owner);
                    } while (inference.did_anything_since_last_call_inside_propagator());

                    return PropagatorState::Enable;
                },
                triggers);
        }
        else
            propagators.install(
                owner,
                [stages = legacy_stages, needs_mult = needs_mult, encoding = legacy_encoding, bit_products_handle = bit_products_handle,
                    mult_q = mult_q, mult_y = mult_y, mult_w = mult_w, prune_zero = prune_zero, y = y,
                    owner = owner](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                    do {
                        if (prune_zero && state.in_domain(y, 0_i))
                            inference.infer(logger, y != 0_i, JustifyUsingRUP{Hint_{owner}}, ExplicitReason{ReasonLiterals{}});

                        if (! propagate_stages(stages, state, inference, logger, owner))
                            return PropagatorState::Enable;

                        if (needs_mult)
                            mult_bc::propagate(mult_q, mult_y, mult_w, state, inference, logger, encoding, *bit_products_handle, owner);
                    } while (inference.did_anything_since_last_call_inside_propagator());

                    return PropagatorState::Enable;
                },
                triggers);

        // Tabulation for GAC: enumerate the distinct underlying variables and
        // the auxiliary slot, so a complete assignment fixes x, y, q and r and
        // every rejected leaf refutes against this block by unit propagation
        // alone.
        TabulationVariables enum_vars;
        auto px = ax.var ? optional{enum_vars.position_of(*ax.var)} : nullopt;
        auto py = ay.var ? optional{enum_vars.position_of(*ay.var)} : nullopt;
        auto pout = aout.var ? optional{enum_vars.position_of(*aout.var)} : nullopt;
        // The default divide path materialises no remainder in the proof (cake's rem_* rows range
        // x - w directly, and a rejected (x, y, q) leaf pins magq/absy/w by unit propagation
        // from the assigned q, y so the rem rows refute a wrong remainder), so it enumerates
        // only x, y and q, with no remainder aux and no determined slots.
        bool no_rem_aux = default_divide;
        std::size_t paux = 0;
        if (! no_rem_aux)
            paux = enum_vars.position_of(aux);

        // x and r are each a function of the others, pinned by unit
        // propagation forwards through the stages: q and y assigned pin
        // w = q * y through the multiplication's bit products, and the
        // linear x = w + r stage then pins whichever of x and r is left.
        // q is a function of the others too, but recovering it means
        // going backwards through the multiplication, which unit
        // propagation cannot do; and y is not a function at all, since
        // q = 0 leaves it anywhere bigger than the remainder. Aliasing
        // spoils the argument, so only distinct slots are claimed (the
        // auxiliary is always fresh).
        // On the cake modulus path the aux is the quotient MAGNITUDE |q|; recover the signed
        // quotient sign(x)sign(y)|q| (a magnitude 0 keeps sign 0). Everywhere else the aux is
        // the signed quotient directly.
        bool aux_is_magnitude = default_modulus;
        auto recover_q = [aux_is_magnitude](Integer auxv, Integer xv, Integer yv) -> Integer {
            return (aux_is_magnitude && ((xv >= 0_i) != (yv >= 0_i))) ? -auxv : auxv;
        };

        vector<DeterminedVariable> determined;
        // Only the legacy divide path reaches here with a materialised remainder aux (the cake
        // path sets no_rem_aux); there the aux is the signed remainder r = x - q * y.
        if (expose_quotient && ! no_rem_aux)
            determined.push_back({aux, [ax, ay, aout, px, py, pout](const vector<Integer> & vals) -> optional<Integer> {
                                      auto xv = px ? ax.coeff * vals[*px] + ax.offset : ax.offset;
                                      auto yv = py ? ay.coeff * vals[*py] + ay.offset : ay.offset;
                                      auto qv = pout ? aout.coeff * vals[*pout] + aout.offset : aout.offset;
                                      return xv - qv * yv;
                                  }});
        else if (! expose_quotient && pout && pout != px && pout != py)
            determined.push_back({*aout.var, [ax, ay, aout, px, py, paux, recover_q](const vector<Integer> & vals) -> optional<Integer> {
                                      auto xv = px ? ax.coeff * vals[*px] + ax.offset : ax.offset;
                                      auto yv = py ? ay.coeff * vals[*py] + ay.offset : ay.offset;
                                      auto want = xv - recover_q(vals[paux], xv, yv) * yv;
                                      if ((want - aout.offset) % aout.coeff != 0_i)
                                          return nullopt;
                                      return (want - aout.offset) / aout.coeff;
                                  }});
        // On the magnitude path x is a function of the others only when it has a fixed sign
        // (for x spanning zero, r = 0 leaves x = +/-|q||y| ambiguous). Its sign then fixes
        // the product's sign: x = sign(x)|q||y| + r.
        bool x_fixed_sign = xlo >= 0_i || xhi <= 0_i;
        Integer x_sign = xhi <= 0_i ? -1_i : 1_i;
        if (px && px != py && px != pout && ! no_rem_aux && (! aux_is_magnitude || x_fixed_sign))
            determined.push_back({*ax.var,
                [ax, ay, aout, py, pout, paux, expose_quotient, aux_is_magnitude, x_sign](const vector<Integer> & vals) -> optional<Integer> {
                    auto yv = py ? ay.coeff * vals[*py] + ay.offset : ay.offset;
                    auto outv = pout ? aout.coeff * vals[*pout] + aout.offset : aout.offset;
                    auto auxv = vals[paux];
                    // The remainder is the aux for (legacy) Divide and the exposed slot for
                    // Modulus; x = q * y + r.
                    auto rv = expose_quotient ? auxv : outv;
                    auto want = aux_is_magnitude ? x_sign * auxv * (yv < 0_i ? -yv : yv) + outv : (expose_quotient ? outv : auxv) * yv + rv;
                    if ((want - ax.offset) % ax.coeff != 0_i)
                        return nullopt;
                    return (want - ax.offset) / ax.coeff;
                }});

        if (want_tabulation(level, enum_vars.vars(), determined, initial_state)) {
            auto accept = [ax, ay, aout, px, py, pout, paux, no_rem_aux, expose_quotient, recover_q](const vector<Integer> & vals) -> bool {
                auto xv = px ? ax.coeff * vals[*px] + ax.offset : ax.offset;
                auto yv = py ? ay.coeff * vals[*py] + ay.offset : ay.offset;
                auto outv = pout ? aout.coeff * vals[*pout] + aout.offset : aout.offset;
                // The default divide path enumerates no remainder aux: q is the exposed slot and
                // the remainder is derived. Elsewhere the aux is the remainder (legacy Divide)
                // or the quotient magnitude (Modulus).
                if (no_rem_aux)
                    return is_in_relation(xv, yv, outv, xv - outv * yv);
                auto auxv = vals[paux];
                auto qv = expose_quotient ? outv : recover_q(auxv, xv, yv);
                auto rv = expose_quotient ? auxv : outv;
                return is_in_relation(xv, yv, qv, rv);
            };

            install_tabulation<Hint_>(propagators, owner, enum_vars.vars(), move(determined), nullopt, accept, expose_quotient ? "divtab" : "modtab",
                expose_quotient ? "building GAC table for division" : "building GAC table for modulus");
        }
    }
}

Divide::Divide(IntegerVariableID x, IntegerVariableID y, IntegerVariableID quotient) : _x(x), _y(y), _quotient(quotient)
{
}

auto Divide::with_consistency(DivideConsistency level) -> Divide &
{
    _level = level;
    return *this;
}

auto Divide::clone() const -> unique_ptr<Constraint>
{
    auto cloned = make_unique<Divide>(_x, _y, _quotient);
    cloned->with_consistency(_level);
    return cloned;
}

auto Divide::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    install_divide_modulus<hints::Divide>(constraint_id(), true, _x, _y, _quotient, _level, propagators, initial_state, optional_model);
}

auto Divide::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    // Flat primitive shape `(id divide x y quotient)`, matching cake_pb_cp.
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom("divide"), tracker.s_expr_term_of(_x), tracker.s_expr_term_of(_y),
        tracker.s_expr_term_of(_quotient)});
}

Modulus::Modulus(IntegerVariableID x, IntegerVariableID y, IntegerVariableID remainder) : _x(x), _y(y), _remainder(remainder)
{
}

auto Modulus::with_consistency(ModulusConsistency level) -> Modulus &
{
    _level = level;
    return *this;
}

auto Modulus::clone() const -> unique_ptr<Constraint>
{
    auto cloned = make_unique<Modulus>(_x, _y, _remainder);
    cloned->with_consistency(_level);
    return cloned;
}

auto Modulus::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    install_divide_modulus<hints::Modulus>(constraint_id(), false, _x, _y, _remainder, _level, propagators, initial_state, optional_model);
}

auto Modulus::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    // Flat primitive shape `(id modulus x y remainder)`, matching cake_pb_cp.
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom("modulus"), tracker.s_expr_term_of(_x), tracker.s_expr_term_of(_y),
        tracker.s_expr_term_of(_remainder)});
}
