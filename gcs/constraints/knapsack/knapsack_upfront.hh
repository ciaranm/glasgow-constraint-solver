#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_KNAPSACK_KNAPSACK_UPFRONT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_KNAPSACK_KNAPSACK_UPFRONT_HH

#include <gcs/constraint.hh>
#include <gcs/constraint_id.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs::innards
{
    /**
     * \brief Install the up-front (paper-style, `ProofLevel::Top`) proof-logging
     * variant of the Knapsack propagator, selected by
     * `Knapsack::with_proof_strategy(proof_strategy::Upfront{})`.
     *
     * It builds the statically-reduced layered DAG once from the initial
     * domains, emits per-coordinate `g_up` / `g_dn` reified inequality flags
     * and per-state conjunction flags once at the search root, and prunes items
     * / total bounds with a per-call `JustifyUsingRUP` that RUP-closes through
     * that scaffolding plus the natural per-equation OPB constraints. It draws
     * exactly the same inferences as the default per-call `Knapsack`; only the
     * proof differs (3–6× smaller, but 3.6–18× slower to verify). See
     * `dev_docs/knapsack.md`.
     */
    auto install_knapsack_upfront(Propagators & propagators, State & initial_state, ProofModel * const optional_model, const ConstraintID & owner,
        std::vector<std::vector<Integer>> coeffs, std::vector<IntegerVariableID> vars, std::vector<IntegerVariableID> totals) -> void;
}

#endif
