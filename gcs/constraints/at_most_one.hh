
#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_AT_MOST_ONE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_AT_MOST_ONE_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/variable_id.hh>

#include <tuple>
#include <vector>

namespace gcs
{
    /**
     * \brief At most one of `vars` is allowed to equal `val`.
     *
     * Native propagator with a Count-style proof model: per-var flags
     * defining `flag_i ⇔ var_i = val`, and the OPB constraint
     * `sum_i flag_i ≤ 1`.
     *
     * Propagation rules:
     *   - For each value `v` in the current domain of `val`, count how many
     *     `vars` are fixed to `v`. If at least two are, infer `val ≠ v`.
     *   - If `val` is fixed to `v` and exactly one var is fixed to `v`, infer
     *     `var_j ≠ v` for every other var `var_j`.
     *
     * Both inferences are RUP from the encoding plus the relevant
     * fixed-variable reasons.
     *
     * \ingroup Constraints
     */
    class AtMostOne : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _vars;
        IntegerVariableID _val;
        std::vector<std::tuple<innards::ProofFlag, innards::ProofFlag, innards::ProofFlag>> _flags;

        virtual auto define_proof_model(innards::ProofModel &) -> void;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit AtMostOne(std::vector<IntegerVariableID> vars, IntegerVariableID val);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const std::string & name, const innards::ProofModel * const) const -> std::string override;
    };

    /**
     * \brief At most one of `vars` is allowed to equal `val`, encoded as a
     * SmartTable.
     *
     * Kept as a baseline / benchmarking alternative to the native
     * AtMostOne propagator. Prefer AtMostOne for production use.
     *
     * \ingroup Constraints
     */
    class AtMostOneSmartTable : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _vars;
        IntegerVariableID _val;

    public:
        explicit AtMostOneSmartTable(std::vector<IntegerVariableID> vars, IntegerVariableID val);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
