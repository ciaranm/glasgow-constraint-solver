#include <gcs/proof_options.hh>

using namespace gcs;

ProofOptions::ProofOptions(const std::string & o, const std::string & p) :
    opb_file(o),
    proof_file(p)
{
}

ProofOptions::ProofOptions(const std::string & o, const std::string & p, bool u) :
    opb_file(o),
    proof_file(p),
    use_friendly_names(u)
{
}
