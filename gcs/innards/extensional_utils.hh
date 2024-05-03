#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_EXTENSIONAL_UTILS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_EXTENSIONAL_UTILS_HH

#include <gcs/extensional.hh>
#include <gcs/innards/inference_tracker-fwd.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <optional>
#include <utility>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief Data for gcs::innards::propagate_extensional().
     *
     * \ingroup Innards
     */
    struct ExtensionalData
    {
        IntegerVariableID selector;
        std::vector<IntegerVariableID> vars;
        ExtensionalTuples tuples;
    };

    /**
     * \brief Propagator for extensional constraints.
     *
     * This function performs propagation for the Table constraint, but also for
     * various other constraints that end up producing something table-like.
     *
     * \sa Table
     */
    auto propagate_extensional(const ExtensionalData &, const State &, InferenceTracker &,
        innards::ProofLogger * const) -> PropagatorState;
}

#endif
