#include <gcs/innards/proofs/constraint_proof_model_data.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>

#include <optional>
#include <string>

using namespace gcs;
using namespace gcs::innards;

using std::optional;
using std::string;

auto gcs::innards::constraint_row_label_from(const ProofLogger & logger, const ConstraintID & id, const string & role) -> optional<ProofLineLabel>
{
    return logger.names_and_ids_tracker().constraint_row_label(id, role);
}
