#include <gcs/constraints/minus.hh>
#include <gcs/constraints/plus.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

using namespace gcs;
using namespace gcs::innards;

using std::optional;
using std::pair;
using std::unique_ptr;

Minus::Minus(IntegerVariableID a, IntegerVariableID b, IntegerVariableID result) :
    _a(a),
    _b(b),
    _result(result)
{
}

auto Minus::clone() const -> unique_ptr<Constraint>
{
    return make_unique<Minus>(_a, _b, _result);
}

auto Minus::install(Propagators & propagators, State &, ProofModel * const optional_model) && -> void
{
    Triggers triggers;
    triggers.on_bounds.insert(triggers.on_change.end(), {_a, _b, _result});

    pair<optional<ProofLine>, optional<ProofLine>> sum_line;
    if (optional_model) {
        sum_line = optional_model->add_constraint("Minus", "sum", WeightedPseudoBooleanSum{} + 1_i * _a + -1_i * _b == 1_i * _result);
    }

    propagators.install(
        [a = _a, b = _b, result = _result, sum_line = sum_line](
            const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            return propagate_plus(a, -b, result, state, inference, logger, sum_line);
        },
        triggers, "plus");
}
