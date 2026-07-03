#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_GLOBAL_CARDINALITY_BOUNDS_GLOBAL_CARDINALITY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_GLOBAL_CARDINALITY_BOUNDS_GLOBAL_CARDINALITY_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <optional>
#include <utility>
#include <vector>

namespace gcs
{
    namespace innards
    {
        /**
         * \brief The bounds-consistency GlobalCardinality propagator, extracted from
         * BoundsGlobalCardinality's install_propagators so the forthcoming merged
         * GlobalCardinality can dispatch to it. Behaviour is unchanged.
         */
        [[nodiscard]] auto propagate_bounds_global_cardinality(const std::vector<IntegerVariableID> & vars, const ConstraintID & owner,
            const std::vector<Integer> & values, const std::vector<IntegerVariableID> & counts,
            const std::vector<std::pair<std::optional<ProofLine>, std::optional<ProofLine>>> & count_lines,
            const std::vector<IntegerVariableID> & all_vars, const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState;
    }

}

#endif
