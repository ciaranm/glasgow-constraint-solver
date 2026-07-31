#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_KNAPSACK_KNAPSACK_UPFRONT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_KNAPSACK_KNAPSACK_UPFRONT_HH

#include <gcs/constraint.hh>
#include <gcs/constraint_id.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <memory>
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
    struct KnapsackUpfrontData;

    /**
     * \brief Validate the arguments, build the statically-reduced DAG from the
     * initial domains, and allocate the dead-state cache. Knapsack::prepare() calls
     * this; the returned data carries everything the other two phases need.
     */
    [[nodiscard]] auto knapsack_upfront_prepare(State & initial_state, std::vector<std::vector<Integer>> coeffs, std::vector<IntegerVariableID> vars,
        std::vector<IntegerVariableID> totals) -> std::shared_ptr<KnapsackUpfrontData>;

    /**
     * \brief Emit the per-equation totals equalities, recording their lines for the
     * propagator's pol steps. Knapsack::define_proof_model() calls this.
     */
    auto knapsack_upfront_define_proof_model(ProofModel & model, const ConstraintID & owner, KnapsackUpfrontData & data) -> void;

    /**
     * \brief Install the root scaffolding initialiser and the propagator.
     * Knapsack::install_propagators() calls this.
     */
    auto knapsack_upfront_install_propagators(
        Propagators & propagators, const ConstraintID & owner, const std::shared_ptr<KnapsackUpfrontData> & data) -> void;
}

#endif
