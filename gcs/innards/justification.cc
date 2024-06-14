#include <gcs/innards/justification.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>

using std::optional;
using std::pair;

using namespace gcs;
using namespace gcs::innards;

auto gcs::innards::add_dependency(RUPDependencies & deps, const optional<RUPDependency> & d) -> void
{
    if (d)
        deps.push_back(*d);
}

auto gcs::innards::add_dependency(RUPDependencies & deps, const pair<optional<ProofLine>, optional<ProofLine>> & d) -> void
{
    if (d.first)
        deps.push_back(*d.first);
    if (d.second)
        deps.push_back(*d.second);
}
