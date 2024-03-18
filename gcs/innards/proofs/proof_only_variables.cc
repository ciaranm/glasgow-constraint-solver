#include <gcs/innards/proofs/proof_only_variables.hh>

using std::string;
using std::to_string;
using std::visit;

using namespace gcs;
using namespace gcs::innards;

auto gcs::innards::operator!(const ProofFlag & f) -> ProofFlag
{
    return ProofFlag{f.index, ! f.positive};
}

auto gcs::innards::operator!(const ProofLiteral & f) -> ProofLiteral
{
    return visit([&](const auto & f) -> ProofLiteral { return ! f; }, f);
}

auto gcs::innards::operator!(const ProofLiteralOrFlag & f) -> ProofLiteralOrFlag
{
    return visit([&](const auto & f) -> ProofLiteralOrFlag { return ! f; }, f);
}

auto gcs::innards::debug_string(const ProofOnlySimpleIntegerVariableID & var) -> string
{
    return "proofvaridx " + to_string(var.index);
}
