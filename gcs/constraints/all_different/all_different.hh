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
     * consistency (the default), bounds consistency, or value consistency (the
     * weakest, cheapest level, which only removes a fixed variable's value from
     * the others).
     *
     * Bounds consistency here is bounds(Z): it reads only each variable's
     * bounds, so it neither sees a hole in a domain nor makes one. On domains
     * with no holes it leaves exactly the bounds generalised arc consistency
     * would, differing only in the interior values arc consistency also
     * removes; once something else has made holes it can leave weaker bounds
     * too, since arc consistency can use a hole to close a Hall set.
     *
     * That does not make bounds consistency safe whenever the rest of the
     * model leaves holes alone, because the holes arc consistency makes itself
     * stay made, and later in the search they can move bounds that bounds
     * consistency cannot. On magic squares, Langford's problem and orthogonal
     * Latin squares it searches more nodes, up to three times as many, and
     * Sudoku puzzles that arc consistency solves without search are out of its
     * reach from 16 by 16 up. Where the holes do not help, as on Golomb rulers
     * (benchmarks/golomb), the search is identical and bounds consistency is
     * several times cheaper per call.
     *
     * \ingroup Consistency
     */
    using AllDifferentConsistency = std::variant<consistency::GAC, consistency::BC, consistency::VC>;

    /**
     * \brief All different constraint: every variable must take a distinct value.
     *
     * Defaults to generalised arc consistency; request consistency::BC for the
     * Hall interval propagator, or consistency::VC for the cheaper
     * value-consistent one. The propagator functions themselves live in
     * gac_all_different.{hh,cc}, bc_all_different.{hh,cc} and
     * vc_all_different.{hh,cc}, which this class dispatches between; the choice
     * selects propagation strength only and never changes the OPB encoding.
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
        virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit AllDifferent(std::vector<IntegerVariableID> vars);

        /// Select the consistency level: consistency::GAC (the default),
        /// consistency::BC, or consistency::VC. Requesting an unsupported level
        /// is a compile-time error, and the choice never changes the OPB
        /// encoding.
        auto with_consistency(AllDifferentConsistency level) -> AllDifferent &;

        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
