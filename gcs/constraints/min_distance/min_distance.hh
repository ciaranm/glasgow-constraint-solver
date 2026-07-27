#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MIN_DISTANCE_MIN_DISTANCE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MIN_DISTANCE_MIN_DISTANCE_HH

#include <gcs/array_param.hh>
#include <gcs/constraint.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <optional>
#include <vector>

namespace gcs
{
    /**
     * \brief Propagation strength for the MinDistance constraint.
     *
     * These select propagation strength only and never change the OPB encoding
     * (define_proof_model is identical for all three). Following Lagerkvist,
     * "Propagation Algorithms for the Minimum-Distance Constraint over Selected
     * Points" (ModRef 2026), Sections 4.1-4.2:
     *
     * - \c CheckOnly: the constraint only acts once the endpoints of a pair are
     *   assigned (the phase-2 baseline; the encoding regression check).
     * - \c ForwardBound: the paper's global-forward-bound. When one endpoint of
     *   a pair is assigned it prunes unsupported values from the other, and it
     *   maintains a pairwise objective upper bound on \c z (the \c pair-forward-bound
     *   filtering, aggregated into one global propagator).
     * - \c PairSupport: the paper's global-pair-support. ForwardBound plus a full
     *   per-pair support scan that can delete unsupported values from either
     *   endpoint before it is assigned.
     *
     * \ingroup Constraints
     */
    enum class MinDistancePropagation
    {
        CheckOnly,
        ForwardBound,
        PairSupport
    };

    /**
     * \brief Constrain \c z to be the minimum, over all pairs of selected-point
     * variables, of the distance between the sites they select.
     *
     * The selected-point variables \f$x_0, \ldots, x_{p-1}\f$ each range over
     * candidate site indices \f$\{0, \ldots, n-1\}\f$, and \c D is a symmetric
     * \f$n \times n\f$ integer distance matrix with a zero diagonal and
     * non-negative entries. The constraint enforces
     * \f[ z = \min_{0 \le i < j < p} D[x_i, x_j]. \f]
     * Duplicate selections are permitted: assigning two positions to the same
     * site \c a contributes the diagonal distance \f$D[a,a] = 0\f$, so \c z is
     * at most zero in that case.
     *
     * The optional requirements matrix \c R (a \f$p \times p\f$ matrix, of which
     * only the entries with \f$i < j\f$ are read) additionally imposes the
     * pairwise lower bounds \f$D[x_i, x_j] \ge R_{ij}\f$ for every \f$i < j\f$.
     * This is the p-dispersion "distance requirements" variant; see Lagerkvist,
     * "Propagation Algorithms for the Minimum-Distance Constraint over Selected
     * Points", ModRef 2026.
     *
     * \c p must be at least two. The distance matrix must be square, symmetric,
     * have a zero diagonal, and non-negative entries; the requirements matrix, if
     * present, must be \f$p \times p\f$ with non-negative entries above the
     * diagonal. Violations are rejected at post time.
     *
     * The \c propagation argument selects the propagation strength (see
     * MinDistancePropagation); it never changes the proof encoding. The default
     * is \c ForwardBound.
     *
     * \ingroup Constraints
     */
    class MinDistance : public Constraint
    {
    public:
        /// A symmetric distance matrix or a requirements matrix.
        using Matrix = std::vector<std::vector<Integer>>;

    private:
        const std::vector<IntegerVariableID> _x;
        const IntegerVariableID _z;
        ArrayParam<Matrix> _distances;
        std::optional<ArrayParam<Matrix>> _requirements;
        MinDistancePropagation _propagation;

        // Filled in by prepare() for use by define_proof_model(): the site
        // values each position can take (visible-frame, one list per position),
        // their union, and z's initial bounds. These flow from prepare() to the
        // proof model per the split-install pattern.
        std::vector<std::vector<Integer>> _position_sites;
        std::vector<Integer> _sites;
        Integer _z_lower = 0_i, _z_upper = 0_i;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;
        auto install_check_only_propagator(innards::Propagators &) -> void;
        auto install_forward_propagator(innards::Propagators &, bool pair_support) -> void;

    public:
        explicit MinDistance(std::vector<IntegerVariableID> x, IntegerVariableID z, ArrayParam<Matrix> distances,
            std::optional<ArrayParam<Matrix>> requirements = std::nullopt, MinDistancePropagation propagation = MinDistancePropagation::ForwardBound);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
