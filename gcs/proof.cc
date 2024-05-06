#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/proofs/variable_constraints_tracker.hh>
#include <gcs/proof.hh>

using namespace gcs;
using namespace gcs::innards;

using std::string;

ProofOptions::ProofOptions(string o, string p) :
    opb_file(move(o)),
    proof_file(move(p))
{
}

ProofOptions::ProofOptions(string o, string p, bool u, bool e, bool r) :
    opb_file(move(o)),
    proof_file(move(p)),
    use_friendly_names(u),
    always_use_full_encoding(e),
    use_reasons(r)
{
}

struct Proof::Imp
{
    VariableConstraintsTracker tracker;
    ProofLogger logger;
    ProofModel model;

    Imp(const ProofOptions & o) :
        tracker(o),
        logger(o, tracker),
        model(o, tracker)
    {
    }
};

Proof::Proof(const ProofOptions & o) :
    _imp(new Imp{o})
{
    _imp->tracker.start_writing_model(model());
}

Proof::~Proof() = default;

auto Proof::logger() -> innards::ProofLogger *
{
    return &_imp->logger;
}

auto Proof::model() -> innards::ProofModel *
{
    return &_imp->model;
}
