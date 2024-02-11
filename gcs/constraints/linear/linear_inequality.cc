#include <gcs/constraints/linear/linear_inequality.hh>
#include <gcs/constraints/linear/propagate.hh>
#include <gcs/constraints/linear/utils.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

using namespace gcs;
using namespace gcs::innards;

using std::nullopt;
using std::optional;
using std::pair;
using std::unique_ptr;

LinearInequality::LinearInequality(WeightedSum coeff_vars, Integer value) :
    _coeff_vars(move(coeff_vars)),
    _value(value)
{
}

auto LinearInequality::clone() const -> unique_ptr<Constraint>
{
    return make_unique<LinearInequality>(WeightedSum{_coeff_vars}, _value);
}

auto LinearInequality::install(Propagators & propagators, State &, ProofModel * const optional_model) && -> void
{
    optional<ProofLine> proof_line;
    if (optional_model) {
        WeightedPseudoBooleanSum terms;
        for (auto & [c, v] : _coeff_vars.terms)
            terms += c * v;
        proof_line = optional_model->add_constraint(terms <= _value, nullopt);
    }

    auto [sanitised_cv, modifier] = tidy_up_linear(_coeff_vars);

    if (visit([](const auto & s) { return s.terms.empty(); }, sanitised_cv) && modifier > _value) {
        propagators.install([](State & state, ProofLogger * const logger) -> pair<Inference, PropagatorState> {
            return pair{state.infer(logger, FalseLiteral{}, JustifyUsingRUP{}), PropagatorState::Enable};
        },
            Triggers{}, "empty linear equality");
    }

    Triggers triggers;
    for (auto & [_, v] : _coeff_vars.terms)
        triggers.on_bounds.push_back(v);

    overloaded{
        [&, &modifier = modifier](const SumOf<Weighted<SimpleIntegerVariableID>> & lin) {
            propagators.install([modifier = modifier, lin = lin, value = _value, proof_line = proof_line](State & state, ProofLogger * const logger) {
                return propagate_linear(lin, value + modifier, state, logger, false, proof_line);
            },
                triggers, "linear inequality");
        },
        [&, &modifier = modifier](const SumOf<PositiveOrNegative<SimpleIntegerVariableID>> & sum) {
            propagators.install([modifier = modifier, sum = sum, value = _value, proof_line = proof_line](State & state, ProofLogger * const logger) {
                return propagate_sum(sum, value + modifier, state, logger, false, proof_line);
            },
                triggers, "linear inequality");
        },
        [&, &modifier = modifier](const SumOf<SimpleIntegerVariableID> & sum) {
            propagators.install([modifier = modifier, sum = sum, value = _value, proof_line = proof_line](State & state, ProofLogger * const logger) {
                return propagate_sum_all_positive(sum, value + modifier, state, logger, false, proof_line);
            },
                triggers, "linear inequality");
        }}
        .visit(sanitised_cv);
}

auto LinearInequality::describe_for_proof() -> std::string
{
    return "linear inequality";
}
