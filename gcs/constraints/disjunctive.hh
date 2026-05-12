#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DISJUNCTIVE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DISJUNCTIVE_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <cstddef>
#include <vector>

namespace gcs
{
    /**
     * \brief Disjunctive (1D non-overlap) constraint, basic case: tasks with
     * variable origins and constant durations. No two tasks may occupy the
     * same time point.
     *
     * A task <em>i</em> is active at time <em>t</em> iff
     * <em>starts[i] &le; t &lt; starts[i] + lengths[i]</em>. For every pair of
     * distinct tasks one of them must finish before the other starts: either
     * <em>starts[i] + lengths[i] &le; starts[j]</em> or
     * <em>starts[j] + lengths[j] &le; starts[i]</em>.
     *
     * The <em>strict</em> flag controls how zero-length tasks are handled.
     * In strict mode (the default), zero-length tasks must still respect the
     * pairwise non-overlap clause &mdash; equivalent to MiniZinc's
     * <code>disjunctive_strict</code>, XCSP3's <code>zeroIgnored = false</code>,
     * and CPMpy's <code>NoOverlap</code>. In non-strict mode, zero-length
     * tasks are dropped at install time and place no constraint on the other
     * tasks &mdash; equivalent to MiniZinc's <code>disjunctive</code> and
     * XCSP3's <code>zeroIgnored = true</code>. Because lengths are constant,
     * the distinction is fully resolved at construction.
     *
     * Propagation is a pure feasibility check: the propagator fires only when
     * every start variable is fixed and then verifies that no pair overlaps.
     * Stronger reasoning (time-table, edge-finding, not-first/not-last) is
     * left for future work.
     *
     * \ingroup Constraints
     */
    class Disjunctive : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _starts;
        std::vector<Integer> _lengths;
        bool _strict;
        std::vector<std::size_t> _active_tasks;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit Disjunctive(std::vector<IntegerVariableID> starts,
            std::vector<Integer> lengths,
            bool strict = true);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
