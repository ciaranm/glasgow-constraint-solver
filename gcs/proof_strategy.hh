#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOF_STRATEGY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOF_STRATEGY_HH

namespace gcs
{
    /**
     * \defgroup ProofStrategy Selecting a proof-logging strategy
     *
     * A handful of constraints — the decision-diagram family `Regular`, `MDD`,
     * `Knapsack` and `BinPacking` — can log their reasoning in more than one
     * way. Every strategy draws exactly the same inferences and finds exactly
     * the same solutions; they differ only in the shape and size of the VeriPB
     * proof, and hence in how quickly that proof verifies. A constraint that
     * offers a choice exposes a `with_proof_strategy()` fluent setter taking a
     * `std::variant` over the tag types below that name exactly the strategies
     * it supports, defaulted to the one that is fastest to verify in practice,
     * for example
     *
     * \code{.cc}
     * problem.post(Knapsack{coeffs, vars, totals}.with_proof_strategy(proof_strategy::Upfront{}));
     * \endcode
     *
     * Requesting a strategy a constraint does not support is a compile-time
     * error: the setter's signature is the documentation. Because the choice
     * is proof-only, it never changes the constraint's meaning, the inferences
     * it draws, the solutions it finds, or the OPB encoding written for the
     * proof — only the proof steps that justify those inferences. When proof
     * logging is switched off, the choice has no effect at all.
     *
     * See `dev_docs/decision-diagram-proof-strategies.md` for the cost model
     * that motivates each default.
     */

    namespace proof_strategy
    {
        /**
         * \brief Emit proof scaffolding lazily, during search: on each
         * propagation call the propagator writes the justification it needs at
         * that node (at `ProofLevel::Current` or `ProofLevel::Temporary`).
         *
         * This keeps the permanent proof database small at the cost of
         * re-deriving per-call material, and is typically the fastest to
         * verify — it is the default for `Knapsack` and `BinPacking`. See
         * `dev_docs/decision-diagram-proof-strategies.md`.
         *
         * \ingroup ProofStrategy
         */
        struct PerCall final
        {
        };

        /**
         * \brief Emit the proof scaffolding once, up front at the search root
         * (at `ProofLevel::Top`), so the per-call propagator's inferences
         * RUP-close through it instead of re-deriving material on every call.
         *
         * This generally produces smaller proofs, but with a wider permanent
         * proof database each RUP can be more expensive to check. It is the
         * default for the narrow-automaton `Regular`, where the fixed scaffold
         * is tiny; for `Knapsack` and `BinPacking` it is the opt-in that
         * trades verify time for proof size. See
         * `dev_docs/decision-diagram-proof-strategies.md`.
         *
         * \ingroup ProofStrategy
         */
        struct Upfront final
        {
        };

        /**
         * \brief Emit a stronger up-front encoding, following Bacchus's "GAC
         * via unit propagation" (CP 2007), so that the per-call propagator can
         * justify its prunes with no proof lines at all — VeriPB closes the
         * eventual backtrack by unit propagation on the Top-level encoding.
         *
         * Specific to `Regular`, whose layer-uniform automaton makes the
         * transition-extension encoding cheap. See
         * `dev_docs/decision-diagram-proof-strategies.md`.
         *
         * \ingroup ProofStrategy
         */
        struct Bacchus final
        {
        };
    }
}

#endif
