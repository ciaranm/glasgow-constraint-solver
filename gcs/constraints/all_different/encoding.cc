#include <gcs/constraints/all_different/encoding.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>

using std::map;
using std::vector;

using namespace gcs;
using namespace gcs::innards;

auto gcs::innards::define_clique_not_equals_encoding(ProofModel & model, const vector<gcs::IntegerVariableID> & vars) -> void
{
    for (unsigned i = 0; i < vars.size(); ++i)
        for (unsigned j = i + 1; j < vars.size(); ++j) {
            auto selector = model.create_proof_flag("notequals");
            model.add_constraint("AllDifferent", "not equals because lower", WPBSum{} + 1_i * vars[i] + -1_i * vars[j] <= -1_i, HalfReifyOnConjunctionOf{selector});
            model.add_constraint("AllDifferent", "not equals because higher", WPBSum{} + -1_i * vars[i] + 1_i * vars[j] <= -1_i, HalfReifyOnConjunctionOf{! selector});
        }
}

auto gcs::innards::define_clique_not_equals_except_encoding(ProofModel & model,
    const vector<gcs::IntegerVariableID> & vars,
    const vector<gcs::Integer> & excluded) -> map<IntegerVariableID, ProofFlag>
{
    map<IntegerVariableID, ProofFlag> duplicate_selectors;

    for (unsigned i = 0; i < vars.size(); ++i)
        for (unsigned j = i + 1; j < vars.size(); ++j) {
            auto selector = model.create_proof_flag("notequals_except");
            HalfReifyOnConjunctionOf lower_conj{selector};
            HalfReifyOnConjunctionOf higher_conj{! selector};
            for (const auto & s : excluded) {
                lower_conj.emplace_back(vars[i] != s);
                lower_conj.emplace_back(vars[j] != s);
                higher_conj.emplace_back(vars[i] != s);
                higher_conj.emplace_back(vars[j] != s);
            }
            model.add_constraint("AllDifferentExcept", "not equals because lower",
                WPBSum{} + 1_i * vars[i] + -1_i * vars[j] <= -1_i, lower_conj);
            model.add_constraint("AllDifferentExcept", "not equals because higher",
                WPBSum{} + -1_i * vars[i] + 1_i * vars[j] <= -1_i, higher_conj);

            if (vars[i] == vars[j])
                duplicate_selectors.insert_or_assign(vars[i], selector);
        }

    return duplicate_selectors;
}
