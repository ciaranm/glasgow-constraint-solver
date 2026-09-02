#include <gcs/constraints/innards/graph_rules.hh>
#include <gcs/innards/proofs/proof_model.hh>

#include <vector>

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::innards::graph_rules;

using std::vector;

namespace
{
    auto half_reify(const vector<IntegerVariableCondition> & conds) -> HalfReifyOnConjunctionOf
    {
        HalfReifyOnConjunctionOf result;
        for (const auto & c : conds)
            result.push_back(ProofLiteral{Literal{c}});
        return result;
    }
}

auto gcs::innards::graph_rules::define(ProofModel & model, const ConstraintID & id, const vector<Rule> & rules) -> void
{
    for (const auto & rule : rules) {
        if (const auto * at_most = std::get_if<AtMost>(&rule)) {
            WPBSum sum;
            for (const auto & v : at_most->vars)
                sum += 1_i * (v == 1_i);
            if (at_most->conds.empty())
                model.add_labelled_constraint(id, at_most->role, move(sum) <= at_most->limit);
            else
                model.add_labelled_constraint(id, at_most->role, move(sum) <= at_most->limit, half_reify(at_most->conds));
        }
        else {
            const auto & selected = std::get<Selected>(rule);
            auto sum = WPBSum{} + 1_i * (selected.var == 1_i);
            if (selected.conds.empty())
                model.add_labelled_constraint(id, selected.role, move(sum) >= 1_i);
            else
                model.add_labelled_constraint(id, selected.role, move(sum) >= 1_i, half_reify(selected.conds));
        }
    }
}

auto gcs::innards::graph_rules::variables_of(const vector<Rule> & rules) -> vector<IntegerVariableID>
{
    vector<IntegerVariableID> result;
    for (const auto & rule : rules) {
        const vector<IntegerVariableCondition> * conds = nullptr;
        if (const auto * at_most = std::get_if<AtMost>(&rule)) {
            result.insert(result.end(), at_most->vars.begin(), at_most->vars.end());
            conds = &at_most->conds;
        }
        else {
            const auto & selected = std::get<Selected>(rule);
            result.push_back(selected.var);
            conds = &selected.conds;
        }
        for (const auto & c : *conds)
            result.push_back(c.var);
    }
    return result;
}
