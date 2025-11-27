#include <gcs/constraints/all_different/encoding.hh>
#include <gcs/innards/proofs/proof_model.hh>

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
