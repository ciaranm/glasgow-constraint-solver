#include <gcs/constraints/plus.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <sstream>

using namespace gcs;
using namespace gcs::innards;

using std::optional;
using std::pair;
using std::stringstream;
using std::unique_ptr;

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

auto Plus::install(Propagators & propagators, State &, ProofModel * const optional_model) && -> void
{
    Triggers triggers;
    triggers.on_bounds.insert(triggers.on_change.end(), {_a, _b, _result});

    pair<optional<ProofLine>, optional<ProofLine>> sum_line;
    if (optional_model) {
        sum_line = optional_model->add_constraint("Plus", "sum", WeightedPseudoBooleanSum{} + 1_i * _a + 1_i * _b == 1_i * _result);
    }

    propagators.install(
        [a = _a, b = _b, result = _result, sum_line = sum_line](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            return propagate_plus(a, b, result, state, inference, logger, sum_line);
        },
        triggers, "plus");
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
            [c, sum_line, logger](const Reason & reason) {
                if (! (c == Conclude::LE ? sum_line.first : sum_line.second))
                    return;

                stringstream pol;
                pol << "pol " << (c == Conclude::LE ? sum_line.first.value() : sum_line.second.value()) << " ";

                overloaded{
                    [&](const XLiteral & x) { pol << logger->names_and_ids_tracker().pb_file_string_for(x) << " +"; },
                    [&](const ProofLine & x) { pol << x << " +"; }}
                    .visit(logger->names_and_ids_tracker().need_pol_item_defining_literal(get<IntegerVariableCondition>(reason().at(0))));

                pol << " ";

                overloaded{
                    [&](const XLiteral & x) { pol << logger->names_and_ids_tracker().pb_file_string_for(x) << " +"; },
                    [&](const ProofLine & x) { pol << x << " +"; }}
                    .visit(logger->names_and_ids_tracker().need_pol_item_defining_literal(get<IntegerVariableCondition>(reason().at(1))));

                logger->emit_proof_line(pol.str(), ProofLevel::Temporary);
            }};
    };

    // min(result) = min(a) + min(b);
    inference.infer(logger, result >= a_vals.first + b_vals.first,
        justify(Conclude::LE),
        [=]() { return Literals{a >= a_vals.first, b >= b_vals.first}; });

    // max(result) = max(a) + max(b);
    inference.infer(logger, result < 1_i + a_vals.second + b_vals.second,
        justify(Conclude::GE),
        [=]() { return Literals{a < a_vals.second + 1_i, b < b_vals.second + 1_i}; });

    // min(a) = min(result) - max(b);
    inference.infer(logger, a >= result_vals.first - b_vals.second,
        justify(Conclude::GE),
        [=]() { return Literals{result >= result_vals.first, b < b_vals.second + 1_i}; });

    // max(a) = max(result) - min(b);
    inference.infer(logger, a < 1_i + result_vals.second - b_vals.first,
        justify(Conclude::LE),
        [=]() { return Literals{result < result_vals.second + 1_i, b >= b_vals.first}; });

    // min(b) = min(result) - max(a);
    inference.infer(logger, b >= result_vals.first - a_vals.second,
        justify(Conclude::GE),
        [=]() { return Literals{result >= result_vals.first, a < a_vals.second + 1_i}; });

    // max(b) = max(result) - min(a);
    inference.infer(logger, b < 1_i + result_vals.second - a_vals.first,
        justify(Conclude::LE),
        [=]() { return Literals{result < result_vals.second + 1_i, a >= a_vals.first}; });

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
