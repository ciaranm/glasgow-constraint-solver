#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_BIN_PACKING_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_BIN_PACKING_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/state.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <memory>
#include <optional>
#include <utility>
#include <vector>

namespace gcs
{
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
        const bool _bounds_only;

        std::shared_ptr<DagBridge> _bridge;
        std::optional<innards::ConstraintStateHandle> _graph_idx;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        /**
         * \brief Variable-load form: `loads[b]` equals the sum of sizes of
         * items assigned to bin `b`. Items must take values in
         * `0..loads.size() - 1`.
         */
        explicit BinPacking(std::vector<IntegerVariableID> items,
            std::vector<Integer> sizes,
            std::vector<IntegerVariableID> loads,
            bool bounds_only = false);

        /**
         * \brief Constant-capacity form: the sum of sizes of items assigned
         * to bin `b` must not exceed `capacities[b]`. Items must take values
         * in `0..capacities.size() - 1`.
         */
        explicit BinPacking(std::vector<IntegerVariableID> items,
            std::vector<Integer> sizes,
            std::vector<Integer> capacities,
            bool bounds_only = false);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
