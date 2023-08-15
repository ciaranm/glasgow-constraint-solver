#include <gcs/proof_options.hh>

using namespace gcs;

using std::string;

ProofOptions::ProofOptions(string o, string p) :
    opb_file(move(o)),
    proof_file(move(p))
{
}

ProofOptions::ProofOptions(string o, string p, bool u, bool e) :
    opb_file(move(o)),
    proof_file(move(p)),
    use_friendly_names(u),
    always_use_full_encoding(e)
{
}
