#include <gcs/innards/proofs/proof_error.hh>

using namespace gcs;
using namespace gcs::innards;

using std::string;

ProofError::ProofError(const string & w) :
    _wat("unexpected problem: " + w)
{
}

auto ProofError::what() const noexcept -> const char *
{
    return _wat.c_str();
}
