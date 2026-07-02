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
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_model.hh>
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

using std::make_unique;
using std::max;
using std::min;
using std::move;
using std::nullopt;
using std::numeric_limits;
using std::optional;
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

        // The exposed slot is the user's; the other is an auxiliary, with
        // bounds tightened by the sign-of-dividend rule where easy.
        IntegerVariableID q = 0_c, r = 0_c;
        SimpleIntegerVariableID aux = SimpleIntegerVariableID{0};
        if (expose_quotient) {
            q = out;
            auto r_lo = xlo >= 0_i ? 0_i : -rmax;
            auto r_hi = xhi <= 0_i ? 0_i : rmax;
            aux = initial_state.allocate_integer_variable_with_state(r_lo, r_hi);
            if (optional_model)
                optional_model->set_up_integer_variable(aux, r_lo, r_hi, "aux_divide_remainder" + to_string(aux.index), nullopt);
            r = aux;
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

        if (! needs_mult) {
            // one of d * q + r - x = 0 (constant divisor) or c * y + r - x = 0
            // (Divide with a constant quotient)
            if (! ay.var)
                add_equality(WeightedSum{} + ay.offset * q + 1_i * r + -1_i * x, 0_i, "sum");
            else
                add_equality(WeightedSum{} + aq.offset * y + 1_i * r + -1_i * x, 0_i, "sum");
        }
        else {
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

            auto [qblo, qbhi] = initial_state.bounds(q);
            auto w_lo = min({qblo * ylo, qblo * yhi, qbhi * ylo, qbhi * yhi});
            auto w_hi = max({qblo * ylo, qblo * yhi, qbhi * ylo, qbhi * yhi});
            auto w = initial_state.allocate_integer_variable_with_state(w_lo, w_hi);
            if (optional_model)
                optional_model->set_up_integer_variable(
                    w, w_lo, w_hi, (expose_quotient ? "aux_divide_product" : "aux_modulus_product") + to_string(w.index), nullopt);

            if (optional_model)
                encoding = mult_bc::define_encoding(*optional_model, initial_state, label, "", q_eff, y_eff, w);
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

Divide::Divide(IntegerVariableID x, IntegerVariableID y, IntegerVariableID quotient, DivideConsistency level) :
    _x(x), _y(y), _quotient(quotient), _level(level)
{
}

auto Divide::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Divide>(_x, _y, _quotient, _level);
}

auto Divide::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    install_divide_modulus<hints::Divide>(constraint_id(), true, _x, _y, _quotient, _level, propagators, initial_state, optional_model);
}

auto Divide::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom("divide"),
        SExpr::list({tracker.s_expr_term_of(_x), tracker.s_expr_term_of(_y), tracker.s_expr_term_of(_quotient)})});
}

Modulus::Modulus(IntegerVariableID x, IntegerVariableID y, IntegerVariableID remainder, ModulusConsistency level) :
    _x(x), _y(y), _remainder(remainder), _level(level)
{
}

auto Modulus::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Modulus>(_x, _y, _remainder, _level);
}

auto Modulus::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    install_divide_modulus<hints::Modulus>(constraint_id(), false, _x, _y, _remainder, _level, propagators, initial_state, optional_model);
}

auto Modulus::s_expr(const ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom("modulus"),
        SExpr::list({tracker.s_expr_term_of(_x), tracker.s_expr_term_of(_y), tracker.s_expr_term_of(_remainder)})});
}
