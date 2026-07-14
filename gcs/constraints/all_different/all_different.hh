#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_DIFFERENT_ALL_DIFFERENT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ALL_DIFFERENT_ALL_DIFFERENT_HH

#include <gcs/consistency.hh>
#include <gcs/constraint.hh>
#include <gcs/constraints/all_different/gac_all_different.hh>
#include <gcs/constraints/all_different/vc_all_different.hh>
#include <gcs/variable_id.hh>

#include <optional>
#include <variant>
#include <vector>

namespace gcs
{
    /**
     * \brief The consistency levels supported by AllDifferent: generalised arc
     * consistency (the default), or value consistency (the weakest, cheapest
     * level, which only removes a fixed variable's value from the others).
     *
     * \ingroup Consistency
     */
    using AllDifferentConsistency = std::variant<consistency::GAC, consistency::VC>;

    /**
     * \brief All different constraint: every variable must take a distinct value.
     *
     * Defaults to generalised arc consistency; request consistency::VC for the
     * cheaper value-consistent propagator. The propagator functions themselves
     * live in gac_all_different.{hh,cc} and vc_all_different.{hh,cc}, which this
     * class dispatches between; the choice selects propagation strength only and
     * never changes the OPB encoding.
     *
     * \ingroup Constraints
     * \sa NValue
     */
    class AllDifferent : public Constraint
    {
    private:
        const std::vector<IntegerVariableID> _vars;
        std::vector<IntegerVariableID> _sanitised_vars;
        std::vector<Integer> _compressed_vals;             ///< consistency::GAC path
        innards::ConstraintStateHandle _unassigned_handle; ///< VC's whole propagator, staged GAC's cheap first stage
        bool _gac_staged = false;                          ///< GAC path: big enough to stage? set in prepare()
        bool _has_duplicate_vars = false;
        AllDifferentConsistency _level = consistency::GAC{};

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit AllDifferent(std::vector<IntegerVariableID> vars);

        /// Select the consistency level: consistency::GAC (the default) or
        /// consistency::VC. Requesting an unsupported level is a compile-time
        /// error, and the choice never changes the OPB encoding.
        auto with_consistency(AllDifferentConsistency level) -> AllDifferent &;

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
