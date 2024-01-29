#include <gcs/constraints/linear/linear_inequality.hh>
#include <gcs/constraints/linear/propagate.hh>
#include <gcs/constraints/linear/utils.hh>
#include <gcs/innards/proof.hh>
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

auto LinearInequality::install(Propagators & propagators, State & initial_state) && -> void
{
    optional<ProofLine> proof_line;
    if (propagators.want_definitions()) {
        WeightedPseudoBooleanSum terms;
        for (auto & [c, v] : _coeff_vars.terms)
            terms += c * v;
        proof_line = propagators.define(initial_state, terms <= _value, nullopt);
    }

    auto [sanitised_cv, modifier] = tidy_up_linear(_coeff_vars);

    if (visit([](const auto & s) { return s.terms.empty(); }, sanitised_cv) && modifier > _value) {
        propagators.install([](State & state) -> pair<Inference, PropagatorState> {
            return pair{state.infer(FalseLiteral{}, JustifyUsingRUP{}), PropagatorState::Enable};
        },
            Triggers{}, "empty linear equality");
    }

    Triggers triggers;
    for (auto & [_, v] : _coeff_vars.terms)
        triggers.on_bounds.push_back(v);

    overloaded{
        [&, &modifier = modifier](const SumOf<Weighted<SimpleIntegerVariableID>> & lin) {
            propagators.install([modifier = modifier, lin = lin, value = _value, proof_line = proof_line](State & state) {
                return propagate_linear(lin, value + modifier, state, false, proof_line);
            },
                triggers, "linear inequality");
        },
        [&, &modifier = modifier](const SumOf<PositiveOrNegative<SimpleIntegerVariableID>> & sum) {
            propagators.install([modifier = modifier, sum = sum, value = _value, proof_line = proof_line](State & state) {
                return propagate_sum(sum, value + modifier, state, false, proof_line);
            },
                triggers, "linear inequality");
        },
        [&, &modifier = modifier](const SumOf<SimpleIntegerVariableID> & sum) {
            propagators.install([modifier = modifier, sum = sum, value = _value, proof_line = proof_line](State & state) mutable {
                return propagate_sum_all_positive(sum, value + modifier, state, false, proof_line);
            },
                triggers, "linear inequality");
        }}
        .visit(sanitised_cv);
}

auto LinearInequality::describe_for_proof() -> std::string
{
    return "linear inequality";
}
