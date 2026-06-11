#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/proof.hh>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::string;

ProofFileNames::ProofFileNames(const std::string & s) :
    opb_file(s + ".opb"),
    proof_file(s + ".pbp"),
    variables_map_file(s + ".varmap"),
    s_expr_file(s + ".scp")
{
}

ProofOptions::ProofOptions(const std::string & f) :
    proof_file_names(f)
{
}

ProofOptions::ProofOptions(const ProofFileNames & f) :
    proof_file_names(f)
{
}

struct Proof::Imp
{
    NamesAndIDsTracker tracker;
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
    _imp(make_unique<Imp>(o))
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
