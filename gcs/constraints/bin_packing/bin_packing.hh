#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_BIN_PACKING_BIN_PACKING_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_BIN_PACKING_BIN_PACKING_HH

#include <gcs/consistency.hh>
#include <gcs/constraint.hh>
#include <gcs/innards/state.hh>
#include <gcs/integer.hh>
#include <gcs/proof_strategy.hh>
#include <gcs/variable_id.hh>

#include <memory>
#include <optional>
#include <string>
#include <variant>
#include <vector>

namespace gcs
{
    /**
     * \brief The consistency levels BinPacking supports: per-bin generalised
     * arc consistency (the stronger default — the Stage 2 bounds pass followed
     * by the Stage 3 partial-load DAG sweep), or bounds consistency (the
     * cheaper Stage 2 pass alone). Joint GAC is NP-hard, so consistency::GAC
     * here means per-bin GAC. The choice selects propagation strength only and
     * never changes the OPB encoding.
     *
     * \ingroup Consistency
     */
    using BinPackingConsistency = std::variant<consistency::GAC, consistency::BC>;

    /**
     * \brief The proof-logging strategies BinPacking supports for its Stage 3
     * sweep: proof_strategy::PerCall (the default — reified per-node state
     * flags at Top, per-call RUP prunes) or proof_strategy::Upfront (also
     * derive the full forward/backward chain scaffolding at Top). Both draw
     * the same inferences; PerCall's proofs are smaller and verify faster on
     * the in-tree benchmarks. No effect under consistency::BC (no Stage 3
     * sweep) or with proof logging off.
     *
     * \ingroup ProofStrategy
     */
    using BinPackingProofStrategy = std::variant<proof_strategy::PerCall, proof_strategy::Upfront>;
    /**
     * \brief Bin packing constraint: each item is assigned to exactly one bin
     * (via `items[i]`), and each bin's total assigned size matches its load
     * variable (or stays within its constant capacity).
     *
     * Two forms are provided, corresponding to FlatZinc's
     * `fzn_bin_packing_load` and `fzn_bin_packing_capa` respectively:
     *
     * - <em>Variable loads:</em> `loads[b]` is constrained to equal
     *   `sum_i { sizes[i] : items[i] == b }`. The bin index range is
     *   implicitly `0..loads.size() - 1` and items[i] must lie within that
     *   range. (A single constant capacity reduces to this form by passing
     *   load variables with domain `0..capacity`.)
     *
     * - <em>Constant capacities:</em> `sum_i { sizes[i] : items[i] == b }`
     *   must not exceed `capacities[b]`. The bin range is
     *   `0..capacities.size() - 1`.
     *
     * Item sizes must be non-negative. By default the propagator runs the
     * per-bin Stage 2 bounds pass followed by a Stage 3 partial-load DAG
     * sweep that achieves *per-bin* GAC on the item variables (joint GAC
     * is NP-hard for BinPacking, so we settle for per-bin). Pass
     * `bounds_only = true` to skip the DAG and use the bounds pass alone
     * — cheaper, recommended when the per-bin capacity is much larger
     * than the number of items. See `dev_docs/bin-packing.md`.
     *
     * The Stage 3 DAG sweep supports two proof-emission strategies,
     * selected by `upfront_proof`:
     *
     * - `upfront_proof = false` (the default): only the reified per-node
     *   state flags are defined at `ProofLevel::Top`; every aggregation
     *   is left to the per-call sweep's `JustifyUsingRUP` prunes, which
     *   RUP-close through those flags plus the natural per-bin OPB
     *   equations. This wins on both proof size (6–10× smaller) and
     *   VeriPB verify time (8–16× faster) on the `bin_packing_bench`
     *   instances, so it is the default.
     * - `upfront_proof = true`: an off-by-default opt-in that additionally
     *   derives the full forward/backward chain scaffolding (per-coord
     *   and joint chains, phantom closures, statically-dead-node lines)
     *   once at `ProofLevel::Top`. It produces larger, slower-to-verify
     *   proofs with no measured benefit on the in-tree benchmarks; kept
     *   for robustness and A/B measurement. See `dev_docs/bin-packing.md`
     *   for the measured rationale.
     *
     * \ingroup Constraints
     */
    class BinPacking : public Constraint
    {
    private:
        struct DagBridge;

        std::vector<IntegerVariableID> _items;
        std::vector<Integer> _sizes;
        std::vector<IntegerVariableID> _loads;
        std::vector<Integer> _capacities;
        const bool _have_loads;
        bool _bounds_only = false;
        bool _upfront_proof = false;

        std::shared_ptr<DagBridge> _bridge;
        std::optional<innards::ConstraintStateHandle> _dead_cache_idx;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        /**
         * \brief Variable-load form: `loads[b]` equals the sum of sizes of
         * items assigned to bin `b`. Items must take values in
         * `0..loads.size() - 1`.
         */
        explicit BinPacking(std::vector<IntegerVariableID> items, std::vector<Integer> sizes, std::vector<IntegerVariableID> loads);

        /**
         * \brief Constant-capacity form: the sum of sizes of items assigned
         * to bin `b` must not exceed `capacities[b]`. Items must take values
         * in `0..capacities.size() - 1`.
         */
        explicit BinPacking(std::vector<IntegerVariableID> items, std::vector<Integer> sizes, std::vector<Integer> capacities);

        /// Select the consistency level: consistency::GAC (per-bin GAC, the
        /// default) or consistency::BC (the cheaper bounds pass alone). The
        /// choice selects propagation strength only and never changes the OPB
        /// encoding.
        auto with_consistency(BinPackingConsistency level) -> BinPacking &;

        /// Select the Stage 3 proof-logging strategy: proof_strategy::PerCall
        /// (the default) or proof_strategy::Upfront. Proof-only: it never
        /// changes the inferences drawn or the solutions found, and has no
        /// effect under consistency::BC or with proof logging off.
        auto with_proof_strategy(BinPackingProofStrategy strategy) -> BinPacking &;

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
