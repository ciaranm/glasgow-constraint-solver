#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_DIFFERENT_BC_ALL_DIFFERENT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_DIFFERENT_BC_ALL_DIFFERENT_HH

#include <gcs/constraint_id.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/innards/state.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <map>
#include <memory>
#include <vector>

namespace gcs::innards
{
    struct BcAllDifferentScratch;

    /**
     * \brief Make the reusable working storage for propagate_bc_all_different.
     *
     * One per installed propagator, passed to every call, as for
     * make_gac_all_different_scratch().
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto make_bc_all_different_scratch() -> std::shared_ptr<BcAllDifferentScratch>;

    /**
     * \brief Make all-different bounds consistent: after this, every variable's
     * lower and upper bound can be extended to a solution in which every other
     * variable takes a value between its own bounds.
     *
     * This is bounds(Z) consistency, the level the Hall interval algorithms
     * reach: it reads only bounds, so it neither sees a hole in a domain nor
     * makes one. It is the algorithm of López-Ortiz, Quimper, Tromp and van
     * Beek, "A fast and simple algorithm for bounds consistency of the
     * alldifferent constraint" (IJCAI 2003): sort the variables by their bounds,
     * and sweep them with union-find over the sorted distinct bounds to find the
     * Hall intervals, lower bounds in one pass and upper bounds in a mirrored
     * second one. Those two passes reach the fixpoint of the bounds they read;
     * they repeat only when a bound they wrote landed in a hole, and the state
     * moved it further, so a call always leaves a fixpoint.
     *
     * Each bound moved is justified by a Hall interval found afresh against the
     * current state (see justify_all_different_hall_interval), so the search for
     * it costs nothing when there is no proof. The per-value at-most-one lines it
     * needs are cached in \p value_am1_constraint_numbers, shared across calls.
     *
     * \ingroup Innards
     */
    auto propagate_bc_all_different(const ConstraintID & constraint_id, const std::vector<IntegerVariableID> & vars,
        std::map<Integer, ProofLine> & value_am1_constraint_numbers, BcAllDifferentScratch & scratch, const State & state, auto & inference,
        ProofLogger * const logger) -> PropagatorState;
}

#endif
