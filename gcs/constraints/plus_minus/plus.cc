#include <gcs/constraints/innards/arithmetic_utils.hh>
#include <gcs/constraints/innards/tabulation.hh>
#include <gcs/constraints/innards/triggers.hh>
#include <gcs/constraints/plus_minus/hints.hh>
#include <gcs/constraints/plus_minus/plus.hh>
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
    auto emit_justification(ProofLogger & logger, const Plus & plus, const ReasonLiterals & reason) -> void
    {
        if (! plus.pol_line)
            return;

        PolBuilder b;
        b.add(*plus.pol_line);

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
    auto propagate_plus(IntegerVariableID a, IntegerVariableID b, IntegerVariableID result, const State & state, auto & inference,
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
            return JustifyExplicitly{hints::Plus{owner, sum_line_value}, ThenRUP::Yes};
        };

        // min(result) = min(a) + min(b);
        inference.infer(logger, result >= a_vals.first + b_vals.first, justify(Conclude::LE),
            ExplicitReason{ReasonLiterals{a >= a_vals.first, b >= b_vals.first}});

        // max(result) = max(a) + max(b);
        inference.infer(logger, result <= a_vals.second + b_vals.second, justify(Conclude::GE),
            ExplicitReason{ReasonLiterals{a <= a_vals.second, b <= b_vals.second}});

        // min(a) = min(result) - max(b);
        inference.infer(logger, a >= result_vals.first - b_vals.second, justify(Conclude::GE),
            ExplicitReason{ReasonLiterals{result >= result_vals.first, b <= b_vals.second}});

        // max(a) = max(result) - min(b);
        inference.infer(logger, a <= result_vals.second - b_vals.first, justify(Conclude::LE),
            ExplicitReason{ReasonLiterals{result <= result_vals.second, b >= b_vals.first}});

        // min(b) = min(result) - max(a);
        inference.infer(logger, b >= result_vals.first - a_vals.second, justify(Conclude::GE),
            ExplicitReason{ReasonLiterals{result >= result_vals.first, a <= a_vals.second}});

        // max(b) = max(result) - min(a);
        inference.infer(logger, b <= result_vals.second - a_vals.first, justify(Conclude::LE),
            ExplicitReason{ReasonLiterals{result <= result_vals.second, a >= a_vals.first}});

        return PropagatorState::Enable;
    }
}

Plus::Plus(IntegerVariableID a, IntegerVariableID b, IntegerVariableID result, PlusConsistency level) : _a(a), _b(b), _result(result), _level(level)
{
}

auto Plus::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Plus>(_a, _b, _result, _level);
}

auto Plus::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
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
    // a + b - result is nonzero is a function of the others, and the
    // encoding pins it by unit propagation. Aliased slots make the net
    // coefficient differ from the slot's own: in x + y = x, say, y is
    // determined but x is not.
    vector<DeterminedVariable> determined;
    for (const auto & [pos, v] : enumerate(enum_vars.vars())) {
        auto net = (pa && *pa == pos ? aa.coeff : 0_i) + (pb && *pb == pos ? ab.coeff : 0_i) - (pc && *pc == pos ? ac.coeff : 0_i);
        if (net != 0_i)
            determined.push_back({v, [aa, ab, ac, pa, pb, pc, pos = pos, net](const vector<Integer> & vals) -> optional<Integer> {
                                      auto other = aa.offset + ab.offset - ac.offset;
                                      if (pa && *pa != pos)
                                          other += aa.coeff * vals[*pa];
                                      if (pb && *pb != pos)
                                          other += ab.coeff * vals[*pb];
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
            if (__builtin_add_overflow(av.raw_value, bv.raw_value, &sum))
                return false;
            return sum == cv.raw_value;
        };

        install_tabulation<hints::Plus>(
            propagators, constraint_id(), enum_vars.vars(), move(determined), nullopt, accept, "plustab", "building GAC table for plus");
    }
}

auto Plus::define_proof_model(ProofModel & model) -> void
{
    // cake_pb_cp labels the two halves of the sum: @c[id][le] on the Z >= a + b
    // half (the LE half of the equality) and @c[id][ge] on the Z <= a + b half.
    // Match those so the encoding byte-matches cake. The {LE, GE} return order is
    // unchanged from the unlabelled add_constraint, so _sum_line still feeds the
    // propagator's Conclude::LE/GE paths correctly.
    _sum_line = model.add_labelled_constraint(as_string(_constraint_id), "le", "ge", "Plus", "sum", WPBSum{} + 1_i * _a + 1_i * _b == 1_i * _result);
}

auto Plus::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_bounds.insert(triggers.on_bounds.end(), {_a, _b, _result});

    propagators.install(
        constraint_id(),
        [a = _a, b = _b, result = _result, sum_line = _sum_line, owner = constraint_id()](const State & state, auto & inference,
            ProofLogger * const logger) -> PropagatorState { return propagate_plus(a, b, result, state, inference, logger, sum_line, owner); },
        triggers);
}

auto Plus::s_expr(const innards::ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();

    // cake_pb_cp's binary prim parse wants three flat args (`plus X Y Z`), not a
    // bracketed list, so X op Y = Z reads as rest = [X; Y; Z].
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom("plus"), tracker.s_expr_term_of(_a), tracker.s_expr_term_of(_b),
        tracker.s_expr_term_of(_result)});
}
