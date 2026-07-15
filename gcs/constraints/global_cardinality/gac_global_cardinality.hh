#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_GLOBAL_CARDINALITY_GAC_GLOBAL_CARDINALITY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_GLOBAL_CARDINALITY_GAC_GLOBAL_CARDINALITY_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <memory>
#include <optional>
#include <utility>
#include <vector>

namespace gcs
{
    namespace innards
    {
        struct GacGlobalCardinalityScratch;

        /**
         * \brief Make the reusable working storage for
         * propagate_gac_global_cardinality.
         *
         * Create one per installed propagator (a `shared_ptr` captured into the
         * propagator closure works well) and pass the same object to every
         * call: the propagator clears rather than reallocates its working
         * buffers, so the hot path stops paying for dozens of allocations on
         * every wake. The type is opaque outside gac_global_cardinality.cc.
         *
         * \ingroup Innards
         */
        [[nodiscard]] auto make_gac_global_cardinality_scratch() -> std::shared_ptr<GacGlobalCardinalityScratch>;

        /**
         * \brief The GAC GlobalCardinality propagator (Régin flow), extracted from
         * GACGlobalCardinality's install_propagators so the forthcoming merged
         * GlobalCardinality can dispatch to it. Behaviour is unchanged.
         */
        [[nodiscard]] auto propagate_gac_global_cardinality(const std::vector<IntegerVariableID> & vars, const ConstraintID & owner,
            const std::vector<Integer> & values, const std::vector<IntegerVariableID> & counts, bool closed,
            const std::vector<std::pair<std::optional<ProofLine>, std::optional<ProofLine>>> & count_lines,
            const std::vector<IntegerVariableID> & all_vars, GacGlobalCardinalityScratch & scratch, const State & state, auto & inference,
            ProofLogger * const logger) -> PropagatorState;
    }

}

#endif
