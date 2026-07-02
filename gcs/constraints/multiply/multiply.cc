#include <gcs/constraints/equals.hh>
#include <gcs/constraints/innards/arithmetic_utils.hh>
#include <gcs/constraints/innards/tabulation.hh>
#include <gcs/constraints/innards/triggers.hh>
#include <gcs/constraints/linear/linear_equality.hh>
#include <gcs/constraints/multiply/hints.hh>
#include <gcs/constraints/multiply/multiply.hh>
#include <gcs/constraints/multiply/multiply_bc.hh>
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
using std::optional;
using std::pair;
using std::size_t;
using std::to_string;
using std::unique_ptr;
using std::vector;

namespace
{
    // The resolved form when at least one operand is constant: a linear
    // equality. Used by both install() and s_expr(), which must agree exactly.
    auto linear_for_constant_operand(const AffineForm & a1, const AffineForm & a2, const IntegerVariableID & v1, const IntegerVariableID & v2,
        const IntegerVariableID & result) -> pair<WeightedSum, Integer>
    {
        if ((! a1.var) && (! a2.var))
            return pair{WeightedSum{} + 1_i * result, a1.offset * a2.offset};

        const auto & other = a1.var ? v1 : v2;
        auto constant = a1.var ? a2.offset : a1.offset;
        return pair{WeightedSum{} + constant * other + -1_i * result, 0_i};
    }
}

Multiply::Multiply(IntegerVariableID v1, IntegerVariableID v2, IntegerVariableID result, MultiplyConsistency level) :
    _v1(v1), _v2(v2), _result(result), _level(level)
{
}

auto Multiply::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Multiply>(_v1, _v2, _result, _level);
}

auto Multiply::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    auto a1 = affine_of(_v1), a2 = affine_of(_v2), a3 = affine_of(_result);

    // A constant operand makes this a linear equality, which knows how to
    // tabulate itself for GAC.
    if ((! a1.var) || (! a2.var)) {
        auto [sum, value] = linear_for_constant_operand(a1, a2, _v1, _v2, _result);

        auto linear_level = overloaded{[&](const consistency::BC &) -> LinearEqualityConsistency { return consistency::BC{}; },
            [&](const consistency::GAC &) -> LinearEqualityConsistency { return consistency::GAC{}; },
            [&](const consistency::Auto &) -> LinearEqualityConsistency {
                long long size = 1;
                for (const auto & [_, v] : sum.terms)
                    if (__builtin_mul_overflow(size, initial_state.domain_size(v).raw_value, &size))
                        return consistency::BC{};
                if (size <= default_tabulation_threshold)
                    return consistency::GAC{};
                return consistency::BC{};
            }}.visit(_level);

        LinearEquality resolved{move(sum), value, linear_level};
        resolved.set_constraint_id(constraint_id());
        move(resolved).install(propagators, initial_state, optional_model);
        return;
    }

    // Both operands are genuine variables, possibly through views. MultiplyBC
    // wants three distinct plain variable handles, so: an aliased operand pair
    // gets an auxiliary copy tied with Equals, and anything else that stops
    // the result slot being a plain distinct variable (views, a constant or
    // aliased result) goes through an auxiliary product variable tied back
    // with a linear equality over the affine expansion.
    auto u1 = *a1.var, u2 = *a2.var;

    auto m2 = u2;
    optional<pair<SimpleIntegerVariableID, SimpleIntegerVariableID>> copy_to_make;
    if (u1 == u2) {
        auto [lo, hi] = initial_state.bounds(u2);
        m2 = initial_state.allocate_integer_variable_with_state(lo, hi);
        if (optional_model)
            optional_model->set_up_integer_variable(m2, lo, hi, "aux_multiply_copy" + to_string(m2.index), nullopt);
        copy_to_make = pair{u2, m2};
    }

    bool operands_plain = a1.coeff == 1_i && a1.offset == 0_i && a2.coeff == 1_i && a2.offset == 0_i;
    bool result_plain = a3.var && a3.coeff == 1_i && a3.offset == 0_i;

    optional<SimpleIntegerVariableID> t;
    if (operands_plain && result_plain && *a3.var != u1 && *a3.var != m2 && u1 != m2)
        t = *a3.var;

    bool need_linear = ! t.has_value();
    if (! t) {
        auto [l1, h1] = initial_state.bounds(u1);
        auto [l2, h2] = initial_state.bounds(u2);
        auto lo = min({l1 * l2, l1 * h2, h1 * l2, h1 * h2});
        auto hi = max({l1 * l2, l1 * h2, h1 * l2, h1 * h2});
        t = initial_state.allocate_integer_variable_with_state(lo, hi);
        if (optional_model)
            optional_model->set_up_integer_variable(*t, lo, hi, "aux_multiply_product" + to_string(t->index), nullopt);
    }

    if (copy_to_make) {
        Equals eq{copy_to_make->first, copy_to_make->second};
        eq.set_constraint_id(child_constraint_id(constraint_id(), "copy"));
        move(eq).install(propagators, initial_state, optional_model);
    }

    MultiplyBC mult{u1, m2, *t};
    mult.set_constraint_id(constraint_id());
    move(mult).install(propagators, initial_state, optional_model);

    if (need_linear) {
        // v1 * v2 = (c1 u1 + b1)(c2 u2 + b2) = c1 c2 t + c1 b2 u1 + c2 b1 u2 + b1 b2
        WeightedSum sum;
        sum += (a1.coeff * a2.coeff) * *t;
        if (a1.coeff * a2.offset != 0_i)
            sum += (a1.coeff * a2.offset) * u1;
        if (a2.coeff * a1.offset != 0_i)
            sum += (a2.coeff * a1.offset) * u2;
        sum += -1_i * _result;
        LinearEquality lin{move(sum), -(a1.offset * a2.offset)};
        lin.set_constraint_id(child_constraint_id(constraint_id(), "fold"));
        move(lin).install(propagators, initial_state, optional_model);
    }

    // Tabulation for GAC: enumerate over the distinct underlying variables,
    // mapping values back through the affine forms. The auxiliary variables
    // are not enumerated; their values follow by unit propagation.
    TabulationVariables enum_vars;
    auto p1 = enum_vars.position_of(u1);
    auto p2 = enum_vars.position_of(u2);
    optional<size_t> p3 = a3.var ? optional{enum_vars.position_of(*a3.var)} : nullopt;

    if (want_tabulation(_level, enum_vars.vars(), initial_state)) {
        auto accept = [a1, a2, a3, p1, p2, p3](const vector<Integer> & vals) -> bool {
            auto v1val = a1.coeff * vals[p1] + a1.offset;
            auto v2val = a2.coeff * vals[p2] + a2.offset;
            auto v3val = p3 ? a3.coeff * vals[*p3] + a3.offset : a3.offset;
            auto product = product_if_representable(v1val, v2val);
            return product && *product == v3val;
        };
        install_tabulation<hints::Multiply>(
            propagators, constraint_id(), enum_vars.vars(), accept, "multtab", "building GAC table for multiplication");
    }
}

auto Multiply::s_expr(const ProofModel * const model) const -> SExpr
{
    auto a1 = affine_of(_v1), a2 = affine_of(_v2);

    // The scp records the resolved constraint: a constant operand makes this a
    // linear equality, and delegating gives exactly the term the reader will
    // repost. Tabulation and the auxiliary variables are invisible here, like
    // every other proof-level choice.
    if ((! a1.var) || (! a2.var)) {
        auto [sum, value] = linear_for_constant_operand(a1, a2, _v1, _v2, _result);
        LinearEquality resolved{move(sum), value};
        resolved.set_constraint_id(_constraint_id);
        return resolved.s_expr(model);
    }

    auto & tracker = model->names_and_ids_tracker();
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom("multiply"),
        SExpr::list({tracker.s_expr_term_of(_v1), tracker.s_expr_term_of(_v2), tracker.s_expr_term_of(_result)})});
}
