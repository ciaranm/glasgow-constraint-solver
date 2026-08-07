#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_scaffolding_scope.hh>

using namespace gcs::innards;

ProofScaffoldingScope::ProofScaffoldingScope(ProofLogger & logger) : _logger(logger), _saved(logger.proof_level())
{
    _logger.enter_proof_level(_saved + 1);
}

auto ProofScaffoldingScope::restore() -> void
{
    if (! _restored) {
        _logger.enter_proof_level(_saved);
        _restored = true;
    }
}

ProofScaffoldingScope::~ProofScaffoldingScope()
{
    restore();
    _logger.forget_proof_level(_saved + 2);
}
