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
     * This propagator is deliberately check-only: it updates \c z (and detects a
     * requirement violation) only once the endpoints of a pair are assigned.
     * Every inference it makes is plain reverse unit propagation from the proof
     * encoding.
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

    public:
        explicit MinDistance(std::vector<IntegerVariableID> x, IntegerVariableID z, ArrayParam<Matrix> distances,
            std::optional<ArrayParam<Matrix>> requirements = std::nullopt);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
