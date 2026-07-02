#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/divide_modulus/divide_modulus.hh>
#include <gcs/constraints/divide_modulus/hints.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/innards/arithmetic_utils.hh>
#include <gcs/constraints/innards/tabulation.hh>
#include <gcs/constraints/innards/triggers.hh>
#include <gcs/constraints/linear/linear_equality.hh>
#include <gcs/constraints/linear/linear_greater_than_equal.hh>
#include <gcs/constraints/linear/linear_less_than_equal.hh>
#include <gcs/constraints/multiply/multiply.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

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
using std::size_t;
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
    // (or r = 0). Divide exposes q and creates r as an auxiliary; Modulus the
    // other way around. Aux variables and any tabulation enumerate over the
    // distinct underlying variables plus the auxiliary, so every rejected
    // leaf in the in-proof table derivation refutes by unit propagation
    // against a single child constraint's encoding.
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

        // Biggest possible |y| bounds the remainder: |r| <= max|y| - 1. (If y
        // spans only zero without being a constant, this clamps to r = 0 and
        // the |r| < |y| constraint below contradicts at the root.)
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

        // x = q * y + r. With a constant divisor d this is entirely linear:
        // x = d * q + r. Otherwise, define w = x - r (pinned by propagation
        // whenever x and r are known), and multiply directly into it:
        // q * y = w. Note that this shape matters for soundness, not just
        // strength: for Modulus the quotient is auxiliary and unbranched, so
        // once the user's variables are fixed, the multiplication must
        // determine it (or fail) by propagation alone. MultiplyBC's quotient
        // filtering does exactly that when its arguments are plain variables,
        // which is also why a view divisor is channelled through a plain copy
        // first rather than letting Multiply fold the view into a linear
        // equality (a fold leaves the product and quotient coupled only
        // through a two-unknowns linear, which bounds propagation cannot
        // finish).
        if (! ay.var) {
            auto d = ay.offset;
            LinearEquality lin{WeightedSum{} + d * q + 1_i * r + -1_i * x, 0_i};
            lin.set_constraint_id(child_constraint_id(owner, "sum"));
            move(lin).install(propagators, initial_state, optional_model);
        }
        else {
            auto y_eff = y;
            if (ay.coeff != 1_i || ay.offset != 0_i) {
                auto y_plain = initial_state.allocate_integer_variable_with_state(min(ylo, yhi), max(ylo, yhi));
                if (optional_model)
                    optional_model->set_up_integer_variable(y_plain, min(ylo, yhi), max(ylo, yhi),
                        (expose_quotient ? "aux_divide_divisor" : "aux_modulus_divisor") + to_string(y_plain.index), nullopt);
                LinearEquality channel{WeightedSum{} + 1_i * y_plain + -1_i * y, 0_i};
                channel.set_constraint_id(child_constraint_id(owner, "divisor"));
                move(channel).install(propagators, initial_state, optional_model);
                y_eff = y_plain;
            }

            auto [qlo, qhi] = initial_state.bounds(q);
            auto w_lo = min({qlo * ylo, qlo * yhi, qhi * ylo, qhi * yhi});
            auto w_hi = max({qlo * ylo, qlo * yhi, qhi * ylo, qhi * yhi});
            auto w = initial_state.allocate_integer_variable_with_state(w_lo, w_hi);
            if (optional_model)
                optional_model->set_up_integer_variable(
                    w, w_lo, w_hi, (expose_quotient ? "aux_divide_product" : "aux_modulus_product") + to_string(w.index), nullopt);

            Multiply mult{q, y_eff, w, consistency::BC{}};
            mult.set_constraint_id(child_constraint_id(owner, "product"));
            move(mult).install(propagators, initial_state, optional_model);

            LinearEquality lin{WeightedSum{} + 1_i * w + 1_i * r + -1_i * x, 0_i};
            lin.set_constraint_id(child_constraint_id(owner, "sum"));
            move(lin).install(propagators, initial_state, optional_model);
        }

        // |r| < |y|, plus y != 0, which is where the relational division-by-
        // zero semantics comes from. With a constant divisor the remainder
        // slot's range suffices: it is baked into the auxiliary's bounds for
        // Divide, and posted on the user's remainder for Modulus. With a
        // variable divisor, split on the divisor's sign with half-reified
        // linear inequalities.
        if (! ay.var) {
            if (! expose_quotient) {
                LessThanEqual le{r, constant_variable(rmax)};
                le.set_constraint_id(child_constraint_id(owner, "remrangehi"));
                move(le).install(propagators, initial_state, optional_model);
                GreaterThanEqual ge{r, constant_variable(-rmax)};
                ge.set_constraint_id(child_constraint_id(owner, "remrangelo"));
                move(ge).install(propagators, initial_state, optional_model);
            }
        }
        else {
            NotEquals ne{y, 0_c};
            ne.set_constraint_id(child_constraint_id(owner, "nonzero"));
            move(ne).install(propagators, initial_state, optional_model);

            // y >= 1 -> r <= y - 1 and r >= -y + 1
            LinearLessThanEqualIf pos_le{WeightedSum{} + 1_i * r + -1_i * y, -1_i, y >= 1_i};
            pos_le.set_constraint_id(child_constraint_id(owner, "rangeposhi"));
            move(pos_le).install(propagators, initial_state, optional_model);
            LinearGreaterThanEqualIf pos_ge{WeightedSum{} + 1_i * r + 1_i * y, 1_i, y >= 1_i};
            pos_ge.set_constraint_id(child_constraint_id(owner, "rangeposlo"));
            move(pos_ge).install(propagators, initial_state, optional_model);

            // y <= -1 -> r <= -y - 1 and r >= y + 1
            LinearLessThanEqualIf neg_le{WeightedSum{} + 1_i * r + 1_i * y, -1_i, y < 0_i};
            neg_le.set_constraint_id(child_constraint_id(owner, "rangeneghi"));
            move(neg_le).install(propagators, initial_state, optional_model);
            LinearGreaterThanEqualIf neg_ge{WeightedSum{} + 1_i * r + -1_i * y, 1_i, y < 0_i};
            neg_ge.set_constraint_id(child_constraint_id(owner, "rangeneglo"));
            move(neg_ge).install(propagators, initial_state, optional_model);
        }

        // The remainder takes the sign of the dividend: x >= 0 -> r >= 0 and
        // x <= 0 -> r <= 0. This is what pins truncation: without it, the
        // identity and |r| < |y| admit both the truncated and the floored
        // (quotient, remainder) pair when the signs differ.
        if (ax.var) {
            GreaterThanEqualIf ge{r, 0_c, x >= 0_i};
            ge.set_constraint_id(child_constraint_id(owner, "signpos"));
            move(ge).install(propagators, initial_state, optional_model);
            LessThanEqualIf le{r, 0_c, x < 1_i};
            le.set_constraint_id(child_constraint_id(owner, "signneg"));
            move(le).install(propagators, initial_state, optional_model);
        }
        else {
            if (ax.offset >= 0_i) {
                GreaterThanEqual ge{r, 0_c};
                ge.set_constraint_id(child_constraint_id(owner, "signpos"));
                move(ge).install(propagators, initial_state, optional_model);
            }
            if (ax.offset <= 0_i) {
                LessThanEqual le{r, 0_c};
                le.set_constraint_id(child_constraint_id(owner, "signneg"));
                move(le).install(propagators, initial_state, optional_model);
            }
        }

        // Tabulation for GAC: enumerate the distinct underlying variables and
        // the auxiliary slot, so a complete assignment fixes x, y, q and r and
        // every rejected leaf refutes against a single child's encoding by
        // unit propagation alone.
        TabulationVariables enum_vars;
        auto px = ax.var ? optional{enum_vars.position_of(*ax.var)} : nullopt;
        auto py = ay.var ? optional{enum_vars.position_of(*ay.var)} : nullopt;
        auto pout = aout.var ? optional{enum_vars.position_of(*aout.var)} : nullopt;
        auto paux = enum_vars.position_of(aux);

        if (want_tabulation(level, enum_vars.vars(), initial_state)) {
            auto accept = [ax, ay, aout, px, py, pout, paux, expose_quotient](const vector<Integer> & vals) -> bool {
                auto xv = px ? ax.coeff * vals[*px] + ax.offset : ax.offset;
                auto yv = py ? ay.coeff * vals[*py] + ay.offset : ay.offset;
                auto outv = pout ? aout.coeff * vals[*pout] + aout.offset : aout.offset;
                auto auxv = vals[paux];
                auto qv = expose_quotient ? outv : auxv;
                auto rv = expose_quotient ? auxv : outv;
                return is_in_relation(xv, yv, qv, rv);
            };
            install_tabulation<Hint_>(propagators, owner, enum_vars.vars(), accept, expose_quotient ? "divtab" : "modtab",
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
