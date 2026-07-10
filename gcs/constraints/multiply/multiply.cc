#include <gcs/constraints/innards/arithmetic_utils.hh>
#include <gcs/constraints/innards/tabulation.hh>
#include <gcs/constraints/innards/triggers.hh>
#include <gcs/constraints/linear/hints.hh>
#include <gcs/constraints/linear/linear_equality.hh>
#include <gcs/constraints/linear/propagate.hh>
#include <gcs/constraints/linear/utils.hh>
#include <gcs/constraints/multiply/hints.hh>
#include <gcs/constraints/multiply/multiply.hh>
#include <gcs/constraints/multiply/signed_multiply.hh>
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

Multiply::Multiply(IntegerVariableID v1, IntegerVariableID v2, IntegerVariableID result) : _v1(v1), _v2(v2), _result(result)
{
}

auto Multiply::with_consistency(MultiplyConsistency level) -> Multiply &
{
    _level = level;
    return *this;
}

auto Multiply::clone() const -> unique_ptr<Constraint>
{
    auto cloned = make_unique<Multiply>(_v1, _v2, _result);
    cloned->with_consistency(_level);
    return cloned;
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
                // budget for what the delegated equality will enumerate:
                // the sanitised terms, with the largest-domained one's level
                // left out because MustHold claims every term as determined.
                // This mirrors want_tabulation's Auto rule, which cannot be
                // called directly because LinearEqualityConsistency has no
                // Auto to delegate; keep the two in step.
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
                            if (mul_overflows(size, d.raw_value, &size))
                                return consistency::BC{};
                        }
                        if (size <= default_tabulation_threshold())
                            return consistency::Tabulated{};
                        return consistency::BC{};
                    },
                    tidied);
            }}.visit(_level);

        LinearEquality resolved{move(sum), value};
        resolved.with_consistency(linear_level);
        resolved.set_constraint_id(constraint_id());
        move(resolved).install(propagators, initial_state, optional_model);
        return;
    }

    // Both operands are genuine variables, possibly through views, aliased
    // with each other, or aliased with the result; the result may also be a
    // view or a constant. The encoding rows and the propagation take the
    // actual handles directly: a repeated operand gets one magnitude channel
    // per slot, exactly as cake_pb_cp emits for (multiply X X Z), and the
    // propagator's square case works on the true relation, so x * x = z gets
    // exact square and square-root hull filtering (issue #232).
    auto u1 = *a1.var, u2 = *a2.var;

    auto product_data =
        make_shared<signed_multiply::Data>(signed_multiply::make_data(optional_model, initial_state, constraint_id(), _v1, _v2, _result));

    Triggers triggers;
    for (const auto & v : {_v1, _v2, _result})
        if ((! is_constant_variable(v)) && triggers.on_bounds.end() == std::find(triggers.on_bounds.begin(), triggers.on_bounds.end(), v))
            triggers.on_bounds.emplace_back(v);

    propagators.install(
        constraint_id(),
        [product_data = product_data, owner = constraint_id()](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            do {
                signed_multiply::propagate(*product_data, state, inference, logger, owner);
            } while (inference.did_anything_since_last_call_inside_propagator());
            // Idempotent: the do-while ran signed_multiply::propagate to quiescence
            // (it exits only when a whole pass inferred nothing), so an immediate
            // re-run is a single no-op pass. This needs no 1:1-trigger / non-aliasing
            // assumption -- the loop reaches whatever fixpoint the true relation has,
            // aliased or repeated operands (the square case) included, per the note at
            // the scope above.
            return PropagatorState::EnableButIdempotent;
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
    // cake_pb_cp wants the flat primitive shape `(id multiply X Y Z)`, like the
    // other arithmetic terms (plus/minus), not a nested variable list.
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom("multiply"), tracker.s_expr_term_of(_v1), tracker.s_expr_term_of(_v2),
        tracker.s_expr_term_of(_result)});
}
