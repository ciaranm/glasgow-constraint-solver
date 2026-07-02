#include <gcs/constraints/innards/arithmetic_utils.hh>
#include <gcs/constraints/innards/tabulation.hh>
#include <gcs/constraints/innards/triggers.hh>
#include <gcs/constraints/linear/hints.hh>
#include <gcs/constraints/linear/linear_equality.hh>
#include <gcs/constraints/linear/propagate.hh>
#include <gcs/constraints/linear/utils.hh>
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

        auto linear_level = overloaded{                                                                            //
            [&](const consistency::BC &) -> LinearEqualityConsistency { return consistency::BC{}; },               //
            [&](const consistency::Tabulated &) -> LinearEqualityConsistency { return consistency::Tabulated{}; }, //
            [&](const consistency::Auto &) -> LinearEqualityConsistency {
                // budget for what the delegated equality will enumerate: the
                // sanitised terms, with the largest-domained one's level left
                // out because MustHold claims every term as determined
                auto tidied = tidy_up_linear(sum).first;
                return visit(
                    [&](const auto & cv) -> LinearEqualityConsistency {
                        Integer largest = 0_i;
                        for (const auto & term : cv.terms)
                            largest = max(largest, initial_state.domain_size(get_var(term)));

                        long long size = 1;
                        bool skipped = false;
                        for (const auto & term : cv.terms) {
                            auto d = initial_state.domain_size(get_var(term));
                            if ((! skipped) && d == largest) {
                                skipped = true;
                                continue;
                            }
                            if (__builtin_mul_overflow(size, d.raw_value, &size))
                                return consistency::BC{};
                        }
                        if (size <= default_tabulation_threshold())
                            return consistency::Tabulated{};
                        return consistency::BC{};
                    },
                    tidied);
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

    // One flat encoding block under our own identity, and one propagator over
    // everything (issue #448): the aliased-operand copy channel and the affine
    // fold are linear lines in our block, and the propagator runs the exposed
    // sub-propagations to a local fixpoint.
    WeightedSum copy_sum, fold_sum;
    Integer fold_value = 0_i;
    if (copy_to_make)
        copy_sum = WeightedSum{} + 1_i * copy_to_make->first + -1_i * copy_to_make->second;
    if (need_linear) {
        // v1 * v2 = (c1 u1 + b1)(c2 u2 + b2) = c1 c2 t + c1 b2 u1 + c2 b1 u2 + b1 b2
        fold_sum += (a1.coeff * a2.coeff) * *t;
        if (a1.coeff * a2.offset != 0_i)
            fold_sum += (a1.coeff * a2.offset) * u1;
        if (a2.coeff * a1.offset != 0_i)
            fold_sum += (a2.coeff * a1.offset) * u2;
        fold_sum += -1_i * _result;
        fold_value = -(a1.offset * a2.offset);
    }

    mult_bc::EncodingData encoding;
    optional<pair<optional<ProofLine>, optional<ProofLine>>> copy_lines, fold_lines;
    if (optional_model) {
        encoding = mult_bc::define_encoding(*optional_model, initial_state, as_string(constraint_id()), "", u1, m2, *t);

        auto as_wpb = [](const WeightedSum & ws) {
            WPBSum terms;
            for (const auto & [c, v] : ws.terms)
                terms += c * v;
            return terms;
        };
        if (copy_to_make) {
            auto lines = optional_model->add_labelled_constraint(
                as_string(constraint_id()), "copyle", "copyge", "Multiply", "aliased operand copy", as_wpb(copy_sum) == 0_i);
            copy_lines = pair{optional{lines.first}, optional{lines.second}};
        }
        if (need_linear) {
            auto lines = optional_model->add_labelled_constraint(
                as_string(constraint_id()), "foldle", "foldge", "Multiply", "affine fold", as_wpb(fold_sum) == fold_value);
            fold_lines = pair{optional{lines.first}, optional{lines.second}};
        }
    }

    auto bit_products_handle = initial_state.add_persistent_constraint_state(encoding.initial_bit_products);

    auto [copy_tidied, copy_modifier] = tidy_up_linear(copy_sum);
    auto [fold_tidied, fold_modifier] = tidy_up_linear(fold_sum);

    Triggers triggers;
    vector<SimpleIntegerVariableID> watched{u1, m2, *t};
    if (a3.var && *a3.var != *t)
        watched.push_back(*a3.var);
    for (const auto & v : watched)
        if (std::find(triggers.on_bounds.begin(), triggers.on_bounds.end(), IntegerVariableID{v}) == triggers.on_bounds.end())
            triggers.on_bounds.emplace_back(v);

    propagators.install(
        constraint_id(),
        [u1 = u1, m2 = m2, t = *t, has_copy = copy_to_make.has_value(), has_fold = need_linear, copy_tidied = copy_tidied,
            copy_modifier = copy_modifier, fold_tidied = fold_tidied, fold_modifier = fold_modifier, fold_value = fold_value, copy_lines = copy_lines,
            fold_lines = fold_lines, encoding = encoding, bit_products_handle = bit_products_handle,
            owner = constraint_id()](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            do {
                // propagate_linear signals failure through the tracker's
                // non-throwing path, so check contradicted() after each call
                // before running the next stage on an emptied domain.
                if (has_copy) {
                    visit(
                        [&](const auto & cv) {
                            propagate_linear(
                                cv, 0_i + copy_modifier, state, inference, logger, true, copy_lines, nullopt, hints::LinearEquality{owner});
                        },
                        copy_tidied);
                    if (inference.contradicted())
                        return PropagatorState::Enable;
                }

                mult_bc::propagate(u1, m2, t, state, inference, logger, encoding, bit_products_handle, owner);

                if (has_fold) {
                    visit(
                        [&](const auto & cv) {
                            propagate_linear(
                                cv, fold_value + fold_modifier, state, inference, logger, true, fold_lines, nullopt, hints::LinearEquality{owner});
                        },
                        fold_tidied);
                    if (inference.contradicted())
                        return PropagatorState::Enable;
                }
            } while (inference.did_anything_since_last_call_inside_propagator());

            return PropagatorState::Enable;
        },
        triggers);

    // Tabulation for GAC: enumerate over the distinct underlying variables,
    // mapping values back through the affine forms. The auxiliary variables
    // are not enumerated; their values follow by unit propagation.
    TabulationVariables enum_vars;
    auto p1 = enum_vars.position_of(u1);
    auto p2 = enum_vars.position_of(u2);
    optional<size_t> p3 = a3.var ? optional{enum_vars.position_of(*a3.var)} : nullopt;

    // the result is a function of the operands, and the encoding pins it
    // by unit propagation once they are assigned; an operand would need a
    // nonzero cofactor, so is not claimed. Aliasing spoils this: x * y = x
    // says nothing about x when y = 1.
    vector<DeterminedVariable> determined;
    if (p3 && *p3 != p1 && *p3 != p2)
        determined.push_back({*a3.var, [a1, a2, a3, p1, p2](const vector<Integer> & vals) -> optional<Integer> {
                                  auto v1val = a1.coeff * vals[p1] + a1.offset;
                                  auto v2val = a2.coeff * vals[p2] + a2.offset;
                                  auto product = product_if_representable(v1val, v2val);
                                  if ((! product) || (*product - a3.offset) % a3.coeff != 0_i)
                                      return nullopt;
                                  return (*product - a3.offset) / a3.coeff;
                              }});

    if (want_tabulation(_level, enum_vars.vars(), determined, initial_state)) {
        auto accept = [a1, a2, a3, p1, p2, p3](const vector<Integer> & vals) -> bool {
            auto v1val = a1.coeff * vals[p1] + a1.offset;
            auto v2val = a2.coeff * vals[p2] + a2.offset;
            auto v3val = p3 ? a3.coeff * vals[*p3] + a3.offset : a3.offset;
            auto product = product_if_representable(v1val, v2val);
            return product && *product == v3val;
        };

        install_tabulation<hints::Multiply>(
            propagators, constraint_id(), enum_vars.vars(), move(determined), nullopt, accept, "multtab", "building GAC table for multiplication");
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
