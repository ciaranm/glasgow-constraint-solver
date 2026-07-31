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

auto gcs::innards::add_equality_stage(vector<StageSpec> & specs, const WeightedSum & sum, Integer value, const string & role) -> void
{
    specs.emplace_back(StageSpec{sum, value, true, role, nullopt});
}

auto gcs::innards::add_le_stage(
    vector<StageSpec> & specs, const WeightedSum & sum, Integer value, const string & role, const optional<IntegerVariableCondition> & gate) -> void
{
    specs.emplace_back(StageSpec{sum, value, false, role, gate});
}

auto gcs::innards::emit_stage_rows(ProofModel & model, const ConstraintID & id, vector<StageSpec> & specs) -> void
{
    for (auto & spec : specs) {
        if (spec.equality) {
            auto ll = model.add_labelled_constraint(id, spec.role + "le", spec.role + "ge", as_wpb(spec.sum) == spec.value);
            spec.lines = pair{optional{ll.first}, optional{ll.second}};
        }
        else if (spec.gate)
            spec.lines.first =
                model.add_labelled_constraint(id, spec.role, as_wpb(spec.sum) <= spec.value, HalfReifyOnConjunctionOf{Literal{*spec.gate}});
        else
            spec.lines.first = model.add_labelled_constraint(id, spec.role, as_wpb(spec.sum) <= spec.value);
    }
}

auto gcs::innards::make_stages(const vector<StageSpec> & specs) -> vector<LinearStage>
{
    vector<LinearStage> stages;
    stages.reserve(specs.size());
    for (const auto & spec : specs) {
        auto [tidied, modifier] = tidy_up_linear(spec.sum);
        stages.emplace_back(LinearStage{tidied, spec.value + modifier, spec.equality, spec.lines, spec.gate});
    }
    return stages;
}
