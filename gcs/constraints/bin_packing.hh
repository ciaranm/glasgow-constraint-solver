#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_BIN_PACKING_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_BIN_PACKING_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

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
     * Item sizes must be non-negative. The `bounds_only` flag is reserved
     * for selecting a weaker (and cheaper) propagation strategy once the
     * stronger DAG-based propagator lands; in the current implementation
     * the constraint installs only an all-items-fixed feasibility checker
     * and the flag has no effect on behaviour. See `dev_docs/bin-packing.md`.
     *
     * \ingroup Constraints
     */
    class BinPacking : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _items;
        std::vector<Integer> _sizes;
        std::vector<IntegerVariableID> _loads;
        std::vector<Integer> _capacities;
        const bool _have_loads;
        const bool _bounds_only;

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
