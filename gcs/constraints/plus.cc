#include <gcs/constraints/plus.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
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
    _sum_line = model.add_constraint("Plus", "sum", WPBSum{} + 1_i * _a + 1_i * _b == 1_i * _result);
}

auto Plus::install_propagators(Propagators & propagators) -> void
{
    Triggers triggers;
    triggers.on_bounds.insert(triggers.on_bounds.end(), {_a, _b, _result});

    propagators.install(
        [a = _a, b = _b, result = _result, sum_line = _sum_line](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            return propagate_plus(a, b, result, state, inference, logger, sum_line);
        },
        triggers);
}

auto Plus::s_exprify(const innards::ProofModel * const model) const -> string
{
    stringstream s;

    print(s, "{} plus (", _name);
    print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(_a));
    print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(_b));
    print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(_result));
    print(s, ")");

    return s.str();
}

auto gcs::innards::propagate_plus(IntegerVariableID a, IntegerVariableID b, IntegerVariableID result,
    const State & state,
    auto & inference,
    ProofLogger * const logger,
    const std::pair<std::optional<ProofLine>, std::optional<ProofLine>> & sum_line) -> PropagatorState
{
    auto a_vals = state.bounds(a);
    auto b_vals = state.bounds(b);
    auto result_vals = state.bounds(result);

    enum class Conclude
    {
        GE,
        LE
    };

    auto justify = [&](Conclude c) -> JustifyExplicitlyThenRUP {
        return JustifyExplicitlyThenRUP{
            [c, sum_line, logger](const ReasonFunction & reason) {
                auto sum_line_value = (c == Conclude::LE ? sum_line.first : sum_line.second);
                if (! sum_line_value)
                    return;

                PolBuilder b;
                b.add(*sum_line_value);

                // Constants in WPBSum are baked into the OPB sum_line directly
                // (see emit_inequality_to.cc:58–60), so a reason literal whose
                // variable is a ConstantIntegerVariableID already contributes
                // to sum_line and doesn't need (or have) a pol-side defining
                // line — need_pol_item_defining_literal would throw on it.
                // Issue #166.
                for (size_t i = 0; i < 2; ++i) {
                    auto lit = get<IntegerVariableCondition>(get<Literal>(get<ProofLiteral>(reason().at(i))));
                    if (holds_alternative<ConstantIntegerVariableID>(lit.var))
                        continue;
                    b.add_for_literal(logger->names_and_ids_tracker(), lit);
                }

                b.emit(*logger, ProofLevel::Temporary);
            }};
    };

    // min(result) = min(a) + min(b);
    inference.infer(logger, result >= a_vals.first + b_vals.first,
        justify(Conclude::LE),
        [=]() { return Reason{a >= a_vals.first, b >= b_vals.first}; });

    // max(result) = max(a) + max(b);
    inference.infer(logger, result <= a_vals.second + b_vals.second,
        justify(Conclude::GE),
        [=]() { return Reason{a <= a_vals.second, b <= b_vals.second}; });

    // min(a) = min(result) - max(b);
    inference.infer(logger, a >= result_vals.first - b_vals.second,
        justify(Conclude::GE),
        [=]() { return Reason{result >= result_vals.first, b <= b_vals.second}; });

    // max(a) = max(result) - min(b);
    inference.infer(logger, a <= result_vals.second - b_vals.first,
        justify(Conclude::LE),
        [=]() { return Reason{result <= result_vals.second, b >= b_vals.first}; });

    // min(b) = min(result) - max(a);
    inference.infer(logger, b >= result_vals.first - a_vals.second,
        justify(Conclude::GE),
        [=]() { return Reason{result >= result_vals.first, a <= a_vals.second}; });

    // max(b) = max(result) - min(a);
    inference.infer(logger, b <= result_vals.second - a_vals.first,
        justify(Conclude::LE),
        [=]() { return Reason{result <= result_vals.second, a >= a_vals.first}; });

    return PropagatorState::Enable;
}

template auto gcs::innards::propagate_plus(IntegerVariableID a, IntegerVariableID b, IntegerVariableID result,
    const State & state,
    EagerProofLoggingInferenceTracker & inference,
    ProofLogger * const logger,
    const std::pair<std::optional<ProofLine>, std::optional<ProofLine>> & sum_line) -> PropagatorState;

template auto gcs::innards::propagate_plus(IntegerVariableID a, IntegerVariableID b, IntegerVariableID result,
    const State & state,
    SimpleInferenceTracker & inference,
    ProofLogger * const logger,
    const std::pair<std::optional<ProofLine>, std::optional<ProofLine>> & sum_line) -> PropagatorState;
