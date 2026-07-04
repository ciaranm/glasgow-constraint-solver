#include <gcs/constraints/divide_modulus/divide_modulus.hh>
#include <gcs/constraints/divide_modulus/hints.hh>
#include <gcs/constraints/innards/arithmetic_utils.hh>
#include <gcs/constraints/innards/linear_stages.hh>
#include <gcs/constraints/innards/tabulation.hh>
#include <gcs/constraints/innards/triggers.hh>
#include <gcs/constraints/linear/hints.hh>
#include <gcs/constraints/linear/linear_equality.hh>
#include <gcs/constraints/linear/linear_greater_than_equal.hh>
#include <gcs/constraints/linear/linear_less_than_equal.hh>
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

#include <util/overloaded.hh>

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

        // cake_pb_cp's divide/modulus encoding: the product |q|*|y| lives only in
        // bit-product flags feeding the remainder/identity rows, with no w (and, for
        // divide, no r) in the OPB. We take that path for plain operands with a
        // non-negative dividend, emitting cake's OPB and introducing the internal
        // handles inside the proof; otherwise the legacy two's-complement path below.
        //
        // Divide (use_cake_divide): x >= 0 keeps w = |q||y| and r = x - w non-negative
        // (only the pos rem_* rows and the wlo stage are active). The divisor y and
        // quotient q may take either sign: make_mag's sign-atom-gated channel converts
        // each to |q|, |y|, the remainder-hi stage splits on sign(y), and the five sign
        // clauses pin sign(q). Because w is the magnitude |q||y| (not the signed product
        // q*y), mult_bc is told z_is_magnitude so it bounds w by the operand magnitudes.
        //
        // Modulus (use_cake_modulus): the exposed slot is r, and cake leaves the
        // quotient's magnitude a FREE axis-0 bit-sum with no i[Q] channel. We restrict
        // to x >= 0 and y >= 1, so q >= 0 too and every sign agrees: q's own in-proof
        // bits (registered in cake's naming below) ARE that free magnitude, needing no
        // channel, and r's range/sign come straight off cake's id_*/rng_*/sgn_* rows.
        // Signed dividends (and, for modulus, a signed divisor) stay on the legacy path.
        bool plain_operands = optional_model && ax.coeff == 1_i && ax.offset == 0_i && ay.var && ay.coeff == 1_i && ay.offset == 0_i && aout.var &&
            aout.coeff == 1_i && aout.offset == 0_i;
        bool use_cake_divide = expose_quotient && plain_operands && xlo >= 0_i;
        bool use_cake_modulus = (! expose_quotient) && plain_operands && xlo >= 0_i && ylo >= 1_i;
        bool use_cake = use_cake_divide || use_cake_modulus;

        // The exposed slot is the user's; the other is an auxiliary, with
        // bounds tightened by the sign-of-dividend rule where easy.
        IntegerVariableID q = 0_c, r = 0_c;
        SimpleIntegerVariableID aux = SimpleIntegerVariableID{0};
        if (expose_quotient) {
            q = out;
            auto r_lo = xlo >= 0_i ? 0_i : -rmax;
            auto r_hi = xhi <= 0_i ? 0_i : rmax;
            // The cake path introduces r = x - w in-proof; the form x - w reaches xhi, so
            // r's bits must span [0, xhi] for introduce_bits_of's upper proofgoal. Widen
            // BOTH the solver state and the proof registration to keep the GAC tabulation
            // (which enumerates the solver range) consistent with the proof bits; the
            // rem_* rows still pin r to [0, |y|-1].
            auto r_hi_cake = max(r_hi, xhi);
            aux = initial_state.allocate_integer_variable_with_state(r_lo, use_cake ? r_hi_cake : r_hi);
            if (optional_model && ! use_cake)
                optional_model->set_up_integer_variable(aux, r_lo, r_hi, "aux_divide_remainder" + to_string(aux.index), nullopt);
            else if (optional_model)
                optional_model->register_state_variable_bits_in_proof(aux, r_lo, r_hi_cake, "aux_divide_remainder" + to_string(aux.index));
            r = aux;
        }
        else if (use_cake) {
            r = out;
            // cake leaves the quotient a free axis-0 magnitude sized by the dividend's
            // bit count (q <= x when y >= 1), so its provable range is the bit-implied
            // [0, 2^n - 1]. Give the state the same range (like divide's product w) and
            // register its bits in cake's x[id][0_*][bin] naming with no OPB bounds, so
            // q's own bits ARE the magnitude the bit products multiply.
            auto q_bits = 0_i;
            while (power2(q_bits) <= xhi)
                q_bits += 1_i;
            auto q_bit_max = power2(q_bits) - 1_i;
            aux = initial_state.allocate_integer_variable_with_state(0_i, q_bit_max);
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

        vector<LinearStage> stages;
        auto add_equality = [&](const WeightedSum & sum, Integer value, const string & role) {
            add_equality_stage(stages, optional_model, label, sum, value, role);
        };
        auto add_le = [&](const WeightedSum & sum, Integer value, const string & role, const optional<IntegerVariableCondition> & gate) {
            add_le_stage(stages, optional_model, label, sum, value, role, gate);
        };

        // x = q * y + r. With a constant divisor or a constant quotient the
        // product is a linear term; otherwise, define w = x - r (pinned by
        // propagation whenever x and r are known) and multiply directly into
        // it: q * y = w, on plain variables.
        bool needs_mult = ay.var && aq.var;
        mult_bc::EncodingData encoding;
        optional<ConstraintStateHandle> bit_products_handle;
        SimpleIntegerVariableID mult_q = aux, mult_y = aux, mult_w = aux; // overwritten when needs_mult
        shared_ptr<mult_bc::EncodingData> cake_encoding;
        shared_ptr<vector<LinearStage>> cake_stages;

        if (use_cake && expose_quotient) {
            auto q_eff = *aq.var, y_eff = *ay.var, x_eff = *ax.var;

            cake_encoding = make_shared<mult_bc::EncodingData>();
            auto & enc = *cake_encoding;
            enc.z_product_ge0_gated = false;
            // w is the magnitude |q||y| (not the signed product q*y), so mult_bc bounds
            // it by the operand magnitudes; see EncodingData::z_is_magnitude.
            enc.z_is_magnitude = true;

            // Operand magnitude channels (cake letters: q -> "Z" axis 0, y -> "Y" axis
            // 1), the bit-product flags x[id][i_j][prod], and their sum |q|*|y|.
            auto product_sum = WPBSum{};
            auto make_mag = [&](SimpleIntegerVariableID v, long long axis, const string & letter) -> ProofOnlySimpleIntegerVariableID {
                auto mag_ub = max(abs(initial_state.lower_bound(v)), abs(initial_state.upper_bound(v)));
                auto mag = optional_model->create_proof_only_integer_variable(0_i, mag_ub, "div_mag_" + letter,
                    IntegerVariableProofRepresentation::Bits, CakeBitNaming{owner, {axis}, "bin", nullopt, false, true});
                auto ge0 = HalfReifyOnConjunctionOf{v >= 0_i};
                auto lt0 = HalfReifyOnConjunctionOf{v < 0_i};
                auto pos_ge = optional_model->add_labelled_constraint(
                    label, letter + "ge0_ge", "Divide", "magnitude channel", WPBSum{} + 1_i * v + -1_i * mag >= 0_i, ge0);
                auto pos_le = optional_model->add_labelled_constraint(
                    label, letter + "ge0_le", "Divide", "magnitude channel", WPBSum{} + -1_i * v + 1_i * mag >= 0_i, ge0);
                auto neg_ge = optional_model->add_labelled_constraint(
                    label, letter + "lt0_ge", "Divide", "magnitude channel", WPBSum{} + 1_i * v + 1_i * mag >= 0_i, lt0);
                auto neg_le = optional_model->add_labelled_constraint(
                    label, letter + "lt0_le", "Divide", "magnitude channel", WPBSum{} + -1_i * v + -1_i * mag >= 0_i, lt0);
                enc.channelling_constraints.insert(
                    {v, mult_bc::ChannellingData{pos_ge, pos_le, neg_ge, neg_le, true, initial_state.lower_bound(v) < 0_i}});
                enc.mag_var.insert({v, mag});
                return mag;
            };
            auto mag_z = make_mag(q_eff, 0, "Z");
            auto mag_y = make_mag(y_eff, 1, "Y");
            auto n1 = optional_model->names_and_ids_tracker().num_bits(mag_z);
            auto n2 = optional_model->names_and_ids_tracker().num_bits(mag_y);
            for (Integer i = 0_i; i < n1; ++i) {
                enc.initial_bit_products.emplace_back();
                for (Integer j = 0_i; j < n2; ++j) {
                    auto flag = optional_model->create_proof_flag_fully_reifying(owner, {i.raw_value, j.raw_value}, "prod",
                        WPBSum{} + 1_i * ProofBitVariable{mag_z, i, true} + 1_i * ProofBitVariable{mag_y, j, true} >= 2_i);
                    auto base = "x[" + label + "][" + to_string(i.raw_value) + "_" + to_string(j.raw_value) + "][prod]";
                    enc.initial_bit_products[i.as_index()].emplace_back(
                        mult_bc::BitProductData{flag, ProofLineLabel{base + "[r]"}, ProofLineLabel{base + "[f]"}, nullopt, nullopt});
                    product_sum += power2(i + j) * flag;
                }
            }
            auto neg_product = WPBSum{};
            for (const auto & t : product_sum.terms)
                neg_product += -t.coefficient * t.variable;

            // w = |q||y|: a state variable driving mult_bc::propagate, ranged to hold
            // the full bit-product sum (the magnitude bits can exceed the operands'
            // actual maxima, so this is >= q_hi*y_hi). Its bits are introduced in-proof.
            auto w_hi = (power2(n1) - 1_i) * (power2(n2) - 1_i);
            auto w = initial_state.allocate_integer_variable_with_state(0_i, w_hi);
            mult_q = q_eff, mult_y = y_eff, mult_w = w;

            // rem_* : 0 <= x - |q||y| < |y|, split on sign(x). Only the pos rows are
            // active for non-negative x; |y| is the y magnitude variable mag_y.
            auto xge0 = HalfReifyOnConjunctionOf{x >= 0_i};
            auto xlt0 = HalfReifyOnConjunctionOf{x < 1_i};
            auto rem_pos_lo =
                optional_model->add_labelled_constraint(label, "rem_pos_lo", "Divide", "remainder", neg_product + 1_i * x_eff >= 0_i, xge0);
            auto rem_pos_hi = optional_model->add_labelled_constraint(
                label, "rem_pos_hi", "Divide", "remainder", product_sum + -1_i * x_eff + 1_i * mag_y >= 1_i, xge0);
            optional_model->add_labelled_constraint(label, "rem_neg_hi", "Divide", "remainder", neg_product + -1_i * x_eff >= 0_i, xlt0);
            optional_model->add_labelled_constraint(label, "rem_neg_lo", "Divide", "remainder", product_sum + 1_i * x_eff + 1_i * mag_y >= 1_i, xlt0);

            // Sign clauses (cake's division orientation over the atoms of x, y, q).
            enc.sign_lines.emplace_back(optional_model->add_labelled_constraint(
                label, "sgn_pp", "Divide", "sign", WPBSum{} + 1_i * (x < 1_i) + 1_i * (y < 1_i) + 1_i * (q >= 0_i) >= 1_i));
            enc.sign_lines.emplace_back(optional_model->add_labelled_constraint(
                label, "sgn_nn", "Divide", "sign", WPBSum{} + 1_i * (x >= 0_i) + 1_i * (y >= 0_i) + 1_i * (q >= 0_i) >= 1_i));
            enc.sign_lines.emplace_back(optional_model->add_labelled_constraint(
                label, "sgn_pn", "Divide", "sign", WPBSum{} + 1_i * (x < 1_i) + 1_i * (y >= 0_i) + 1_i * (q < 1_i) >= 1_i));
            enc.sign_lines.emplace_back(optional_model->add_labelled_constraint(
                label, "sgn_np", "Divide", "sign", WPBSum{} + 1_i * (x >= 0_i) + 1_i * (y < 1_i) + 1_i * (q < 1_i) >= 1_i));
            enc.sign_lines.emplace_back(
                optional_model->add_labelled_constraint(label, "sgn_x0", "Divide", "sign", WPBSum{} + 1_i * (x != 0_i) + 1_i * (q < 1_i) >= 1_i));
            optional_model->add_labelled_constraint(
                label, "nonzero", "Divide", "divisor is not zero", WPBSum{} + 1_i * (y >= 1_i) + 1_i * (y < 0_i) >= 1_i);

            // w = |q||y| is a state variable (drives mult_bc::propagate) whose bits are
            // introduced inside the proof, so nothing about it is asserted in the OPB.
            // r is eliminated: cake's rem_* express 0 <= x - w < y directly over w, so r
            // needs no proof presence (it stays an inert state auxiliary here).
            optional_model->register_state_variable_bits_in_proof(w, 0_i, w_hi, "aux_divide_product" + to_string(w.index));
            bit_products_handle = initial_state.add_persistent_constraint_state(enc.initial_bit_products);

            // Stages over w (0 <= x - w < |y|): wlo (w <= x) gated [x>=0]; and the
            // remainder-hi (x - w <= |y| - 1) split on sign(y) so each stage carries a
            // single gate -- x-w-y<=-1 gated [y>=1] (|y|=y), x-w+y<=-1 gated [y<0]
            // (|y|=-y). The stage lines keep rem_*'s [x>=0] gate and the channel's [y
            // sign] gate; propagate_linear's ThenRUP discharges [x>=0] by unit
            // propagation (x's domain lb >= 0) and the [y sign] from the stage gate.
            cake_stages = make_shared<vector<LinearStage>>();
            auto [t_wlo, m_wlo] = tidy_up_linear(WeightedSum{} + 1_i * w + -1_i * x);
            cake_stages->emplace_back(LinearStage{t_wlo, 0_i + m_wlo, false, {nullopt, nullopt}, optional{x_eff >= 0_i}});
            auto [t_whip, m_whip] = tidy_up_linear(WeightedSum{} + 1_i * x + -1_i * w + -1_i * y);
            cake_stages->emplace_back(LinearStage{t_whip, -1_i + m_whip, false, {nullopt, nullopt}, optional{y >= 1_i}});
            auto [t_whin, m_whin] = tidy_up_linear(WeightedSum{} + 1_i * x + -1_i * w + 1_i * y);
            cake_stages->emplace_back(LinearStage{t_whin, -1_i + m_whin, false, {nullopt, nullopt}, optional{y < 0_i}});

            auto y_ge0_ge = enc.channelling_constraints.at(y_eff).pos_ge; // y - mag_y >= 0 gated [y>=0]
            auto y_lt0_le = enc.channelling_constraints.at(y_eff).neg_le; // -y - mag_y >= 0 gated [y<0]
            propagators.install_initialiser([enc = cake_encoding, stg = cake_stages, product_sum, w, w_hi, r = aux, x_eff, rem_pos_lo, rem_pos_hi,
                                                y_ge0_ge, y_lt0_le](State &, auto &, ProofLogger * const logger) -> void {
                if (! logger || logger->get_assertion_level() > AssertionLevel::Off)
                    return;
                // w = |q||y|, introduced as a conservative extension.
                // v3_eq_product_lines = {w >= product, w <= product}.
                enc->v3_eq_product_lines = logger->introduce_bits_of(product_sum, w, ProofLevel::Top);
                // Ungated x - w >= 0 in the DB, so introduce_bits_of(x-w, r) below can
                // auto-prove r's non-negativity: rem_pos_lo (x - product >= 0, gated
                // [x>=0], big-M w_hi) + (product >= w) + w_hi*[x>=0] discharges the gate.
                auto x_ge0 = logger->emit_rup_proof_line(WPBSum{} + 1_i * (x_eff >= 0_i) >= 1_i, ProofLevel::Top);
                PolBuilder pb_xw;
                pb_xw.add(rem_pos_lo).add(enc->v3_eq_product_lines.second).add(x_ge0, w_hi);
                pb_xw.emit(*logger, ProofLevel::Top);
                // r = x - w, introduced so the tabulation's determined r unit-propagates.
                logger->introduce_bits_of(WPBSum{} + 1_i * x_eff + -1_i * w, r, ProofLevel::Top);
                // wlo, [x>=0]-gated (w <= x): rem_pos_lo (x - product >= 0) + (w <= product).
                PolBuilder pb_wlo;
                pb_wlo.add(rem_pos_lo).add(enc->v3_eq_product_lines.second);
                (*stg)[0].lines = {pb_wlo.emit(*logger, ProofLevel::Top), nullopt};
                // whi_ypos (x - w - y <= -1, |y|=y): rem_pos_hi (product - x + |y| >= 1)
                // + (w >= product) + Yge0_ge (y - |y| >= 0). |y| = mag_y cancels; the
                // channel's [y>=0] gate rides along and the stage gates on [y>=1].
                PolBuilder pb_whip;
                pb_whip.add(rem_pos_hi).add(enc->v3_eq_product_lines.first).add(y_ge0_ge);
                (*stg)[1].lines = {pb_whip.emit(*logger, ProofLevel::Top), nullopt};
                // whi_yneg (x - w + y <= -1, |y|=-y): rem_pos_hi + (w >= product)
                // + Ylt0_le (-y - |y| >= 0). Stage gates on [y<0].
                PolBuilder pb_whin;
                pb_whin.add(rem_pos_hi).add(enc->v3_eq_product_lines.first).add(y_lt0_le);
                (*stg)[2].lines = {pb_whin.emit(*logger, ProofLevel::Top), nullopt};
            });
        }
        else if (use_cake) {
            // Modulus's cake path: the exposed slot is r, the quotient q a free axis-0
            // magnitude whose bits (registered above) are its own -- no i[Q], no channel,
            // since q >= 0 means q = |q|. w = q * y (both non-negative) is a product state
            // variable introduced in the proof; r = x - w comes off cake's id_pos rows and
            // 0 <= r < |y| off rng_*. The id_neg_*/rng_lo/sgn_* rows are cake's inert
            // (satisfiable) mirror for x < 0, emitted only to match cake's OPB.
            //
            // The identity stage propagates the exposed r, so r must be the plain underlying
            // variable *aout.var (r_eff), not any view wrapper: propagating a change through
            // a view's deviewed bits while the identity spans the wide product w defeats the
            // reverse unit propagation. The guard's coeff-1/offset-0 restriction makes r_eff
            // exactly the exposed value, and cake names it i[R] too, so this also matches.
            auto q_eff = *aq.var, y_eff = *ay.var, x_eff = *ax.var, r_eff = *aout.var;

            cake_encoding = make_shared<mult_bc::EncodingData>();
            auto & enc = *cake_encoding;
            enc.z_product_ge0_gated = false;
            enc.z_is_magnitude = false; // q, y >= 0, so w = q * y is the plain product

            // Axis-1 magnitude channel for y (cake letter "Y"); q needs none, as its own
            // cake-named bits are the axis-0 magnitude.
            auto mag_y_ub = max(abs(initial_state.lower_bound(y_eff)), abs(initial_state.upper_bound(y_eff)));
            auto mag_y = optional_model->create_proof_only_integer_variable(
                0_i, mag_y_ub, "mod_mag_Y", IntegerVariableProofRepresentation::Bits, CakeBitNaming{owner, {1}, "bin", nullopt, false, true});
            auto y_ge0 = HalfReifyOnConjunctionOf{y_eff >= 0_i};
            auto y_lt0 = HalfReifyOnConjunctionOf{y_eff < 0_i};
            auto y_pos_ge = optional_model->add_labelled_constraint(
                label, "Yge0_ge", "Modulus", "magnitude channel", WPBSum{} + 1_i * y_eff + -1_i * mag_y >= 0_i, y_ge0);
            auto y_pos_le = optional_model->add_labelled_constraint(
                label, "Yge0_le", "Modulus", "magnitude channel", WPBSum{} + -1_i * y_eff + 1_i * mag_y >= 0_i, y_ge0);
            auto y_neg_ge = optional_model->add_labelled_constraint(
                label, "Ylt0_ge", "Modulus", "magnitude channel", WPBSum{} + 1_i * y_eff + 1_i * mag_y >= 0_i, y_lt0);
            auto y_neg_le = optional_model->add_labelled_constraint(
                label, "Ylt0_le", "Modulus", "magnitude channel", WPBSum{} + -1_i * y_eff + -1_i * mag_y >= 0_i, y_lt0);
            enc.channelling_constraints.insert(
                {y_eff, mult_bc::ChannellingData{y_pos_ge, y_pos_le, y_neg_ge, y_neg_le, true, initial_state.lower_bound(y_eff) < 0_i}});
            enc.mag_var.insert({y_eff, mag_y});

            // Bit-product flags x[id][i_j][prod] = q_i ^ mag_y_j and their weighted sum
            // |q|*|y|. q's axis-0 bits are q_eff's own registered (cake-named) bits.
            auto n1 = optional_model->names_and_ids_tracker().num_bits(q_eff);
            auto n2 = optional_model->names_and_ids_tracker().num_bits(mag_y);
            auto product_sum = WPBSum{};
            for (Integer i = 0_i; i < n1; ++i) {
                enc.initial_bit_products.emplace_back();
                for (Integer j = 0_i; j < n2; ++j) {
                    auto flag = optional_model->create_proof_flag_fully_reifying(owner, {i.raw_value, j.raw_value}, "prod",
                        WPBSum{} + 1_i * ProofBitVariable{q_eff, i, true} + 1_i * ProofBitVariable{mag_y, j, true} >= 2_i);
                    auto base = "x[" + label + "][" + to_string(i.raw_value) + "_" + to_string(j.raw_value) + "][prod]";
                    enc.initial_bit_products[i.as_index()].emplace_back(
                        mult_bc::BitProductData{flag, ProofLineLabel{base + "[r]"}, ProofLineLabel{base + "[f]"}, nullopt, nullopt});
                    product_sum += power2(i + j) * flag;
                }
            }
            auto neg_product = WPBSum{};
            for (const auto & t : product_sum.terms)
                neg_product += -t.coefficient * t.variable;

            optional_model->add_labelled_constraint(
                label, "nonzero", "Modulus", "divisor is not zero", WPBSum{} + 1_i * (y >= 1_i) + 1_i * (y < 0_i) >= 1_i);

            // r = x - |q||y|, split on sign(x): id_pos_* (gated [x>=0]) is the active
            // r = x - w equality; id_neg_* (gated [x<0]) its inert mirror.
            auto xge0 = HalfReifyOnConjunctionOf{x_eff >= 0_i};
            auto xlt0 = HalfReifyOnConjunctionOf{x_eff < 1_i};
            auto id_pos_ge = optional_model->add_labelled_constraint(
                label, "id_pos_ge", "Modulus", "identity", neg_product + 1_i * x_eff + -1_i * r_eff >= 0_i, xge0);
            auto id_pos_le = optional_model->add_labelled_constraint(
                label, "id_pos_le", "Modulus", "identity", product_sum + -1_i * x_eff + 1_i * r_eff >= 0_i, xge0);
            optional_model->add_labelled_constraint(label, "id_neg_ge", "Modulus", "identity", neg_product + -1_i * x_eff + 1_i * r_eff >= 0_i, xlt0);
            optional_model->add_labelled_constraint(label, "id_neg_le", "Modulus", "identity", product_sum + 1_i * x_eff + -1_i * r_eff >= 0_i, xlt0);

            // 0 <= r < |y|: rng_hi (r < |y|, active) and rng_lo (r > -|y|, inert), plus
            // the r-sign rows (r takes x's sign; sgn_pos trivial, sgn_neg inert here).
            auto rng_hi = optional_model->add_labelled_constraint(label, "rng_hi", "Modulus", "range", WPBSum{} + -1_i * r_eff + 1_i * mag_y >= 1_i);
            optional_model->add_labelled_constraint(label, "rng_lo", "Modulus", "range", WPBSum{} + 1_i * r_eff + 1_i * mag_y >= 1_i);
            auto sgn_pos = optional_model->add_labelled_constraint(label, "sgn_pos", "Modulus", "sign", WPBSum{} + 1_i * r_eff >= 0_i, xge0);
            optional_model->add_labelled_constraint(label, "sgn_neg", "Modulus", "sign", WPBSum{} + -1_i * r_eff >= 0_i, xlt0);

            // w = |q||y| is a product state variable driving mult_bc, sized to the full
            // bit-product sum; its bits are introduced in the proof.
            auto w_hi = (power2(n1) - 1_i) * (power2(n2) - 1_i);
            auto w = initial_state.allocate_integer_variable_with_state(0_i, w_hi);
            optional_model->register_state_variable_bits_in_proof(w, 0_i, w_hi, "aux_modulus_product" + to_string(w.index));
            mult_q = q_eff, mult_y = y_eff, mult_w = w;
            bit_products_handle = initial_state.add_persistent_constraint_state(enc.initial_bit_products);

            // Stages over the underlying operands: the identity r = x - w (two [x>=0]-gated
            // inequalities off id_pos_*), the range r < |y| (gated [y>=1], off rng_hi + the y
            // channel), and r >= 0 (gated [x>=0], off sgn_pos) which -- since r takes x's sign
            // -- prunes a would-be negative remainder when r's domain spans zero. The gates
            // ride along, discharged by propagate_linear's ThenRUP from x's / y's domains.
            // Proof lines are filled once w = product is introduced in the initialiser.
            cake_stages = make_shared<vector<LinearStage>>();
            auto [t_idle, m_idle] = tidy_up_linear(WeightedSum{} + 1_i * x_eff + -1_i * w + -1_i * r_eff);
            cake_stages->emplace_back(LinearStage{t_idle, 0_i + m_idle, false, {nullopt, nullopt}, optional{x_eff >= 0_i}});
            auto [t_idge, m_idge] = tidy_up_linear(WeightedSum{} + -1_i * x_eff + 1_i * w + 1_i * r_eff);
            cake_stages->emplace_back(LinearStage{t_idge, 0_i + m_idge, false, {nullopt, nullopt}, optional{x_eff >= 0_i}});
            auto [t_rhi, m_rhi] = tidy_up_linear(WeightedSum{} + 1_i * r_eff + -1_i * y_eff);
            cake_stages->emplace_back(LinearStage{t_rhi, -1_i + m_rhi, false, {nullopt, nullopt}, optional{y_eff >= 1_i}});
            auto [t_slo, m_slo] = tidy_up_linear(WeightedSum{} + -1_i * r_eff);
            cake_stages->emplace_back(LinearStage{t_slo, 0_i + m_slo, false, {nullopt, nullopt}, optional{x_eff >= 0_i}});

            propagators.install_initialiser([enc = cake_encoding, stg = cake_stages, product_sum, w, id_pos_ge, id_pos_le, rng_hi, sgn_pos, y_pos_ge](
                                                State &, auto &, ProofLogger * const logger) -> void {
                if (! logger || logger->get_assertion_level() > AssertionLevel::Off)
                    return;
                // w = |q||y|; v3_eq_product_lines = {w >= product, w <= product}.
                enc->v3_eq_product_lines = logger->introduce_bits_of(product_sum, w, ProofLevel::Top);
                // identity r >= x - w (x - w - r <= 0): id_pos_le (r - x + product >= 0)
                // + (w >= product). The [x>=0] gate rides along, discharged by x's domain.
                PolBuilder pb_idle;
                pb_idle.add(id_pos_le).add(enc->v3_eq_product_lines.first);
                (*stg)[0].lines = {pb_idle.emit(*logger, ProofLevel::Top), nullopt};
                // identity r <= x - w (w + r - x <= 0): id_pos_ge (x - product - r >= 0)
                // + (w <= product).
                PolBuilder pb_idge;
                pb_idge.add(id_pos_ge).add(enc->v3_eq_product_lines.second);
                (*stg)[1].lines = {pb_idge.emit(*logger, ProofLevel::Top), nullopt};
                // range r < |y| (r - y <= -1, |y|=y): rng_hi (|y| - r >= 1) + Yge0_ge
                // (y - |y| >= 0); |y| = mag_y cancels, the [y>=0] gate rides along.
                PolBuilder pb_rhi;
                pb_rhi.add(rng_hi).add(y_pos_ge);
                (*stg)[2].lines = {pb_rhi.emit(*logger, ProofLevel::Top), nullopt};
                // r >= 0 (-r <= 0): straight off sgn_pos, [x>=0] gate discharged by x's domain.
                PolBuilder pb_slo;
                pb_slo.add(sgn_pos);
                (*stg)[3].lines = {pb_slo.emit(*logger, ProofLevel::Top), nullopt};
            });
        }

        if (! use_cake && ! needs_mult) {
            // one of d * q + r - x = 0 (constant divisor) or c * y + r - x = 0
            // (Divide with a constant quotient)
            if (! ay.var)
                add_equality(WeightedSum{} + ay.offset * q + 1_i * r + -1_i * x, 0_i, "sum");
            else
                add_equality(WeightedSum{} + aq.offset * y + 1_i * r + -1_i * x, 0_i, "sum");
        }
        else if (! use_cake) {
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
                encoding = mult_bc::define_encoding(*optional_model, initial_state, owner, label, "", q_eff, y_eff, w);
            bit_products_handle = initial_state.add_persistent_constraint_state(encoding.initial_bit_products);
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
        if (! use_cake) {
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
        if (use_cake) {
            propagators.install(
                owner,
                [enc = cake_encoding, stg = cake_stages, bph = *bit_products_handle, mult_q = mult_q, mult_y = mult_y, mult_w = mult_w, y = y,
                    owner = owner](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                    do {
                        if (state.in_domain(y, 0_i))
                            inference.infer(logger, y != 0_i, JustifyUsingRUP{Hint_{owner}}, ExplicitReason{ReasonLiterals{}});

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
                [stages = stages, needs_mult = needs_mult, encoding = encoding, bit_products_handle = bit_products_handle, mult_q = mult_q,
                    mult_y = mult_y, mult_w = mult_w, prune_zero = prune_zero, y = y,
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
        auto paux = enum_vars.position_of(aux);

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
        vector<DeterminedVariable> determined;
        if (expose_quotient)
            determined.push_back({aux, [ax, ay, aout, px, py, pout](const vector<Integer> & vals) -> optional<Integer> {
                                      auto xv = px ? ax.coeff * vals[*px] + ax.offset : ax.offset;
                                      auto yv = py ? ay.coeff * vals[*py] + ay.offset : ay.offset;
                                      auto qv = pout ? aout.coeff * vals[*pout] + aout.offset : aout.offset;
                                      return xv - qv * yv;
                                  }});
        else if (pout && pout != px && pout != py)
            determined.push_back({*aout.var, [ax, ay, aout, px, py, paux](const vector<Integer> & vals) -> optional<Integer> {
                                      auto xv = px ? ax.coeff * vals[*px] + ax.offset : ax.offset;
                                      auto yv = py ? ay.coeff * vals[*py] + ay.offset : ay.offset;
                                      auto want = xv - vals[paux] * yv;
                                      if ((want - aout.offset) % aout.coeff != 0_i)
                                          return nullopt;
                                      return (want - aout.offset) / aout.coeff;
                                  }});
        if (px && px != py && px != pout)
            determined.push_back({*ax.var, [ax, ay, aout, py, pout, paux, expose_quotient](const vector<Integer> & vals) -> optional<Integer> {
                                      auto yv = py ? ay.coeff * vals[*py] + ay.offset : ay.offset;
                                      auto outv = pout ? aout.coeff * vals[*pout] + aout.offset : aout.offset;
                                      auto auxv = vals[paux];
                                      auto qv = expose_quotient ? outv : auxv;
                                      auto rv = expose_quotient ? auxv : outv;
                                      auto want = qv * yv + rv;
                                      if ((want - ax.offset) % ax.coeff != 0_i)
                                          return nullopt;
                                      return (want - ax.offset) / ax.coeff;
                                  }});

        if (want_tabulation(level, enum_vars.vars(), determined, initial_state)) {
            auto accept = [ax, ay, aout, px, py, pout, paux, expose_quotient](const vector<Integer> & vals) -> bool {
                auto xv = px ? ax.coeff * vals[*px] + ax.offset : ax.offset;
                auto yv = py ? ay.coeff * vals[*py] + ay.offset : ay.offset;
                auto outv = pout ? aout.coeff * vals[*pout] + aout.offset : aout.offset;
                auto auxv = vals[paux];
                auto qv = expose_quotient ? outv : auxv;
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
