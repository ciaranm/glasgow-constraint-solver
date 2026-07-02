#include <gcs/constraints/innards/arithmetic_utils.hh>
#include <gcs/constraints/innards/tabulation.hh>
#include <gcs/constraints/innards/triggers.hh>
#include <gcs/constraints/plus_minus/hints.hh>
#include <gcs/constraints/plus_minus/minus.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>

using namespace gcs;
using namespace gcs::innards;

using std::holds_alternative;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::size_t;
using std::unique_ptr;
using std::vector;

namespace gcs::innards::hints
{
    auto emit_justification(ProofLogger & logger, const Minus & minus, const ReasonLiterals & reason) -> void
    {
        if (! minus.pol_line)
            return;

        PolBuilder b;
        b.add(*minus.pol_line);

        // Constants in WPBSum are baked into the OPB sum_line directly (see
        // emit_inequality_to.cc:58-60), so a reason literal whose variable is a
        // ConstantIntegerVariableID already contributes to sum_line and doesn't
        // need (or have) a pol-side defining line. Issue #166.
        for (size_t i = 0; i < 2; ++i) {
            auto lit = get<IntegerVariableCondition>(get<Literal>(get<ProofLiteral>(reason.at(i))));
            if (holds_alternative<ConstantIntegerVariableID>(lit.var))
                continue;
            b.add_for_literal(logger.names_and_ids_tracker(), lit);
        }

        b.emit(logger, ProofLevel::Temporary);
    }
}

namespace
{
    // Direct propagator for a - b = result. Deliberately not implemented via
    // propagate_plus(a, -b, result, ...) — synthesising the -b view inside the
    // propagator means the reason literals end up on an unregistered view of
    // b's underlying variable, and the pol step in the justify callback then
    // mixes V-bits (from the model's sum_line, over the user's b) with
    // X-bits (from the deviewed reason reif), preventing cancellation.
    // Keeping b as the user-supplied variable throughout means PolBuilder's
    // add_for_literal always lands on the registered view.
    auto propagate_minus(IntegerVariableID a, IntegerVariableID b, IntegerVariableID result, const State & state, auto & inference,
        ProofLogger * const logger, const pair<optional<ProofLine>, optional<ProofLine>> & sum_line, const ConstraintID & owner) -> PropagatorState
    {
        auto a_vals = state.bounds(a);
        auto b_vals = state.bounds(b);
        auto result_vals = state.bounds(result);

        enum class Conclude
        {
            GE,
            LE
        };

        auto justify = [&](Conclude c) {
            auto sum_line_value = (c == Conclude::LE ? sum_line.first : sum_line.second);
            return JustifyExplicitly{hints::Minus{owner, sum_line_value}, ThenRUP::Yes};
        };

        // Conclude side picked so the OPB sum_line half contributes the same
        // sign on the variable being bounded as the reasons do, leaving the
        // inferred literal after cancellation. sum_line.first is the "a - b ≤ c"
        // half (-a + b + c >= 0); sum_line.second is "a - b ≥ c" (a - b - c >= 0).

        // min(result) = min(a) - max(b);
        inference.infer(logger, result >= a_vals.first - b_vals.second, justify(Conclude::LE),
            ExplicitReason{ReasonLiterals{a >= a_vals.first, b <= b_vals.second}});

        // max(result) = max(a) - min(b);
        inference.infer(logger, result <= a_vals.second - b_vals.first, justify(Conclude::GE),
            ExplicitReason{ReasonLiterals{a <= a_vals.second, b >= b_vals.first}});

        // min(a) = min(result) + min(b);
        inference.infer(logger, a >= result_vals.first + b_vals.first, justify(Conclude::GE),
            ExplicitReason{ReasonLiterals{result >= result_vals.first, b >= b_vals.first}});

        // max(a) = max(result) + max(b);
        inference.infer(logger, a <= result_vals.second + b_vals.second, justify(Conclude::LE),
            ExplicitReason{ReasonLiterals{result <= result_vals.second, b <= b_vals.second}});

        // min(b) = min(a) - max(result);
        inference.infer(logger, b >= a_vals.first - result_vals.second, justify(Conclude::LE),
            ExplicitReason{ReasonLiterals{a >= a_vals.first, result <= result_vals.second}});

        // max(b) = max(a) - min(result);
        inference.infer(logger, b <= a_vals.second - result_vals.first, justify(Conclude::GE),
            ExplicitReason{ReasonLiterals{a <= a_vals.second, result >= result_vals.first}});

        return PropagatorState::Enable;
    }
}

Minus::Minus(IntegerVariableID a, IntegerVariableID b, IntegerVariableID result, MinusConsistency level) :
    _a(a), _b(b), _result(result), _level(level)
{
}

auto Minus::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Minus>(_a, _b, _result, _level);
}

auto Minus::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);

    // Tabulation for GAC: enumerate the distinct underlying variables, mapping
    // values back through the affine forms.
    auto aa = affine_of(_a), ab = affine_of(_b), ac = affine_of(_result);
    TabulationVariables enum_vars;
    optional<size_t> pa = aa.var ? optional{enum_vars.position_of(*aa.var)} : nullopt;
    optional<size_t> pb = ab.var ? optional{enum_vars.position_of(*ab.var)} : nullopt;
    optional<size_t> pc = ac.var ? optional{enum_vars.position_of(*ac.var)} : nullopt;

    // the relation is linear, so any variable whose net coefficient in
    // a - b - result is nonzero is a function of the others, and the
    // encoding pins it by unit propagation. Aliased slots make the net
    // coefficient differ from the slot's own: in x - y = x, say, y is
    // determined but x is not.
    vector<DeterminedVariable> determined;
    for (const auto & [pos, v] : enumerate(enum_vars.vars())) {
        auto net = (pa && *pa == pos ? aa.coeff : 0_i) - (pb && *pb == pos ? ab.coeff : 0_i) - (pc && *pc == pos ? ac.coeff : 0_i);
        if (net != 0_i)
            determined.push_back({v, [aa, ab, ac, pa, pb, pc, pos = pos, net](const vector<Integer> & vals) -> optional<Integer> {
                                      auto other = aa.offset - ab.offset - ac.offset;
                                      if (pa && *pa != pos)
                                          other += aa.coeff * vals[*pa];
                                      if (pb && *pb != pos)
                                          other -= ab.coeff * vals[*pb];
                                      if (pc && *pc != pos)
                                          other -= ac.coeff * vals[*pc];
                                      if ((-other) % net != 0_i)
                                          return nullopt;
                                      return -other / net;
                                  }});
    }

    if (want_tabulation(_level, enum_vars.vars(), determined, initial_state)) {
        auto accept = [aa, ab, ac, pa, pb, pc](const vector<Integer> & vals) -> bool {
            auto av = pa ? aa.coeff * vals[*pa] + aa.offset : aa.offset;
            auto bv = pb ? ab.coeff * vals[*pb] + ab.offset : ab.offset;
            auto cv = pc ? ac.coeff * vals[*pc] + ac.offset : ac.offset;
            long long sum;
            if (__builtin_add_overflow(av.raw_value, -bv.raw_value, &sum))
                return false;
            return sum == cv.raw_value;
        };

        install_tabulation<hints::Minus>(
            propagators, constraint_id(), enum_vars.vars(), move(determined), nullopt, accept, "minustab", "building GAC table for minus");
    }
}

auto Minus::define_proof_model(ProofModel & model) -> void
{
    // cake_pb_cp labels the two halves of the sum: @c[id][le] on the a - b <= c
    // half (-a + b + c >= 0) and @c[id][ge] on the a - b >= c half (a - b - c >= 0).
    // Match those so the encoding byte-matches cake. The {LE, GE} return order is
    // unchanged from the unlabelled add_constraint, so _sum_line still feeds the
    // propagator's Conclude::LE/GE paths correctly.
    _sum_line =
        model.add_labelled_constraint(as_string(_constraint_id), "le", "ge", "Minus", "sum", WPBSum{} + 1_i * _a + -1_i * _b == 1_i * _result);
}

auto Minus::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_bounds.insert(triggers.on_bounds.end(), {_a, _b, _result});

    propagators.install(
        constraint_id(),
        [a = _a, b = _b, result = _result, sum_line = _sum_line, owner = constraint_id()](const State & state, auto & inference,
            ProofLogger * const logger) -> PropagatorState { return propagate_minus(a, b, result, state, inference, logger, sum_line, owner); },
        triggers);
}

auto Minus::s_expr(const innards::ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();

    // Three flat args (`minus X Y Z`) to match cake_pb_cp's binary prim parse.
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom("minus"), tracker.s_expr_term_of(_a), tracker.s_expr_term_of(_b),
        tracker.s_expr_term_of(_result)});
}
