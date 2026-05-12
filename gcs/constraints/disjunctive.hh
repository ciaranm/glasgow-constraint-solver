#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DISJUNCTIVE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_DISJUNCTIVE_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <cstddef>
#include <map>
#include <utility>
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
     * Propagation is time-table consistent at heights = 1, capacity = 1:
     * mandatory parts of distinct tasks may not overlap, and each task's
     * bounds are pushed away from time points already mandatorily occupied
     * by another. Stronger reasoning (edge-finding, not-first / not-last)
     * is left for future work.
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

        // Per-task possible-active window computed from initial bounds in
        // prepare(). Only populated for positive-length active tasks; indexed
        // by task index into _starts. Used both for sizing the bridge in
        // install_propagators's initialiser and for indexing into per-(task, t)
        // bridge flags from the propagator.
        std::vector<Integer> _per_task_t_lo;
        std::vector<Integer> _per_task_t_hi;

        // Encoded pairwise reified before-flags. The OPB stays purely
        // declarative: for each ordered pair (i, j) of active tasks,
        // before_{i,j} <-> s_i + l_i <= s_j, plus one clause per unordered
        // pair. Line numbers are stored so the propagator's bridge
        // derivations can pol them.
        struct BeforeFlagData
        {
            innards::ProofFlag flag;
            innards::ProofLine forward_line;
            innards::ProofLine reverse_line;
        };
        std::map<std::pair<std::size_t, std::size_t>, BeforeFlagData> _before_flags;
        std::map<std::pair<std::size_t, std::size_t>, innards::ProofLine> _clause_lines;

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
