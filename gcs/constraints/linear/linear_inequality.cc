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
        propagators.install_initialiser([](State & state, ProofLogger * const logger) -> Inference {
            return state.infer(logger, FalseLiteral{}, JustifyUsingRUP{Literals{}});
        });
    }

    Triggers triggers;
    for (auto & [_, v] : _coeff_vars.terms)
        triggers.on_bounds.push_back(v);

    visit(
        [&, &modifier = modifier](const auto & lin) {
            propagators.install([modifier = modifier, lin = lin, value = _value, proof_line = proof_line](
                                    State & state, ProofLogger * const logger) {
                return propagate_linear(lin, value + modifier, state, logger, false, proof_line, nullopt);
            },
                triggers, "linear inequality");
        },
        sanitised_cv);
}

auto LinearInequality::describe_for_proof() -> std::string
{
    return "linear inequality";
}
