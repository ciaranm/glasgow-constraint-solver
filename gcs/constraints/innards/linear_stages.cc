#include <gcs/constraints/innards/linear_stages.hh>
#include <gcs/exception.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/state.hh>

using namespace gcs;
using namespace gcs::innards;

using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::vector;

namespace
{
    auto as_wpb(const WeightedSum & ws) -> WPBSum
    {
        WPBSum terms;
        for (const auto & [c, v] : ws.terms)
            terms += c * v;
        return terms;
    }
}

auto gcs::innards::stage_gate_holds(const State & state, const IntegerVariableCondition & cond) -> bool
{
    switch (cond.op) {
        using enum VariableConditionOperator;
    case GreaterEqual: return state.lower_bound(cond.var) >= cond.value;
    case Less: return state.upper_bound(cond.var) < cond.value;
    case Equal: return state.lower_bound(cond.var) == cond.value && state.upper_bound(cond.var) == cond.value;
    default: throw UnexpectedException{"unexpected stage gate operator"};
    }
}

auto gcs::innards::add_equality_stage(vector<LinearStage> & stages, ProofModel * const model, const ConstraintID & id, const WeightedSum & sum,
    Integer value, const string & role) -> void
{
    pair<optional<ProofLine>, optional<ProofLine>> lines;
    if (model) {
        auto ll = model->add_labelled_constraint(id, role + "le", role + "ge", as_wpb(sum) == value);
        lines = pair{optional{ll.first}, optional{ll.second}};
    }
    auto [tidied, modifier] = tidy_up_linear(sum);
    stages.emplace_back(LinearStage{tidied, value + modifier, true, lines, nullopt});
}

auto gcs::innards::add_le_stage(vector<LinearStage> & stages, ProofModel * const model, const ConstraintID & id, const WeightedSum & sum,
    Integer value, const string & role, const optional<IntegerVariableCondition> & gate) -> void
{
    pair<optional<ProofLine>, optional<ProofLine>> lines;
    if (model) {
        if (gate)
            lines.first = model->add_labelled_constraint(id, role, as_wpb(sum) <= value, HalfReifyOnConjunctionOf{Literal{*gate}});
        else
            lines.first = model->add_labelled_constraint(id, role, as_wpb(sum) <= value);
    }
    auto [tidied, modifier] = tidy_up_linear(sum);
    stages.emplace_back(LinearStage{tidied, value + modifier, false, lines, gate});
}
