#include <gcs/constraints/plus.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>
#include <gcs/innards/state.hh>

#include <sstream>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#endif

using namespace gcs;
using namespace gcs::innards;

using std::holds_alternative;
using std::optional;
using std::pair;
using std::string;
using std::stringstream;
using std::unique_ptr;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

namespace gcs::innards::hints
{
    // Witness for a plus bound push: the sum-definition line to start the cut
    // from. The two operand bounds come from the reason (read positionally), so
    // emit_justification consumes the reason — the opposite of all_different's
    // Hall emit, which ignores it. A genuinely witness-driven emit (nothing
    // captured but the witness and logger), in contrast to all_different's, whose
    // emit must capture per-constraint state. No hint_sexpr overload: plus has no
    // typed external hint yet (its witness is the reason, already in the
    // assertion), so it carries only the coarse hint_name.
    //
    // pol_line is optional: with no sum line (e.g. proofs without a model) there
    // is no explicit lemma, just the trailing RUP, so emit does nothing — an
    // empty-emit explicit step, byte-identical to the pre-witness early return.
    struct PlusBound
    {
        std::optional<ProofLine> pol_line;
        static constexpr std::string_view hint_name = "plus";
    };

    auto emit_justification(ProofLogger & logger, const PlusBound & d, const ReasonLiterals & reason) -> void
    {
        if (! d.pol_line)
            return;

        PolBuilder b;
        b.add(*d.pol_line);

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
    auto propagate_plus(IntegerVariableID a, IntegerVariableID b, IntegerVariableID result,
        const State & state,
        auto & inference,
        ProofLogger * const logger,
        const pair<optional<ProofLine>, optional<ProofLine>> & sum_line) -> PropagatorState
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
            return JustifyExplicitly{hints::PlusBound{sum_line_value}, ThenRUP::Yes};
        };

        // min(result) = min(a) + min(b);
        inference.infer(logger, result >= a_vals.first + b_vals.first,
            justify(Conclude::LE),
            ExplicitReason{ReasonLiterals{a >= a_vals.first, b >= b_vals.first}});

        // max(result) = max(a) + max(b);
        inference.infer(logger, result <= a_vals.second + b_vals.second,
            justify(Conclude::GE),
            ExplicitReason{ReasonLiterals{a <= a_vals.second, b <= b_vals.second}});

        // min(a) = min(result) - max(b);
        inference.infer(logger, a >= result_vals.first - b_vals.second,
            justify(Conclude::GE),
            ExplicitReason{ReasonLiterals{result >= result_vals.first, b <= b_vals.second}});

        // max(a) = max(result) - min(b);
        inference.infer(logger, a <= result_vals.second - b_vals.first,
            justify(Conclude::LE),
            ExplicitReason{ReasonLiterals{result <= result_vals.second, b >= b_vals.first}});

        // min(b) = min(result) - max(a);
        inference.infer(logger, b >= result_vals.first - a_vals.second,
            justify(Conclude::GE),
            ExplicitReason{ReasonLiterals{result >= result_vals.first, a <= a_vals.second}});

        // max(b) = max(result) - min(a);
        inference.infer(logger, b <= result_vals.second - a_vals.first,
            justify(Conclude::LE),
            ExplicitReason{ReasonLiterals{result <= result_vals.second, a >= a_vals.first}});

        return PropagatorState::Enable;
    }
}

Plus::Plus(IntegerVariableID a, IntegerVariableID b, IntegerVariableID result) :
    _a(a),
    _b(b),
    _result(result)
{
}

auto Plus::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Plus>(_a, _b, _result);
}

auto Plus::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    if (! prepare(propagators, initial_state, optional_model))
        return;

    if (optional_model)
        define_proof_model(*optional_model);

    install_propagators(propagators);
}

auto Plus::define_proof_model(ProofModel & model) -> void
{
    // cake_pb_cp labels the two halves of the sum: @c[id][le] on the Z >= a + b
    // half (the LE half of the equality) and @c[id][ge] on the Z <= a + b half.
    // Match those so the encoding byte-matches cake. The {LE, GE} return order is
    // unchanged from the unlabelled add_constraint, so _sum_line still feeds the
    // propagator's Conclude::LE/GE paths correctly.
    _sum_line = model.add_labelled_constraint(as_string(_constraint_id), "le", "ge", "Plus", "sum",
        WPBSum{} + 1_i * _a + 1_i * _b == 1_i * _result);
}

auto Plus::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_bounds.insert(triggers.on_bounds.end(), {_a, _b, _result});

    propagators.install(
        constraint_id(),
        [a = _a, b = _b, result = _result, sum_line = _sum_line](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            return propagate_plus(a, b, result, state, inference, logger, sum_line);
        },
        triggers);
}

auto Plus::s_expr(const innards::ProofModel * const model) const -> SExpr
{
    auto & tracker = model->names_and_ids_tracker();

    // cake_pb_cp's binary prim parse wants three flat args (`plus X Y Z`), not a
    // bracketed list, so X op Y = Z reads as rest = [X; Y; Z].
    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom("plus"),
        tracker.s_expr_term_of(_a),
        tracker.s_expr_term_of(_b),
        tracker.s_expr_term_of(_result)});
}
