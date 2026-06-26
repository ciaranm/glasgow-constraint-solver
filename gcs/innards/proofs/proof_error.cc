#include <gcs/innards/proofs/proof_error.hh>

using namespace gcs;
using namespace gcs::innards;

using std::string;

ProofError::ProofError(const string & w) : MessageException("unexpected problem: " + w)
{
}
