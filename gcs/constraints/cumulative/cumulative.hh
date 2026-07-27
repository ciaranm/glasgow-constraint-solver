#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CUMULATIVE_CUMULATIVE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CUMULATIVE_CUMULATIVE_HH

#include <gcs/constraint.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_only_variables-fwd.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <cstddef>
#include <map>
#include <optional>
#include <vector>

namespace gcs
{
    /**
     * \brief Cumulative constraint: tasks with start times, durations, and
     * demands, sharing a resource of a given capacity. Any of the durations,
     * demands, and the capacity may be variables or constants (constants are
     * passed as ConstantIntegerVariableID). At every time point the sum of
     * demands of currently-active tasks must not exceed the capacity.
     *
     * A task <em>i</em> is active at time <em>t</em> iff
     * <em>starts[i] &le; t &lt; starts[i] + lengths[i]</em>.
     *
     * Propagation is time-table consistent. For each task, the
     * <em>mandatory part</em> is the interval
     * <em>[ub(start), lb(start) + lb(length))</em> &mdash; the time it must
     * occupy regardless of where exactly it starts. Summing the guaranteed
     * demands (lb(height)) over mandatory parts gives a load profile; if that
     * profile exceeds the largest allowed capacity (ub) anywhere, the
     * constraint is infeasible. Each task's bounds are pushed away from any
     * time point where placing it would force the load over capacity. Stronger
     * reasoning (edge-finding, energetic) is left for future work.
     *
     * \ingroup Constraints
     */
    class Cumulative : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _starts;
        std::vector<IntegerVariableID> _lengths;
        std::vector<IntegerVariableID> _heights;
        IntegerVariableID _capacity;
        // Snapshots resolved in prepare(). For each of lengths and heights,
        // _*_vals holds the constant value for a constant argument (and 0 for a
        // variable one, where the variable / _contrib_flags is used instead) and
        // _*_ub holds the initial upper bound (used to size the possible-active
        // window / contrib domain and to filter tasks that can never load).
        // _length_lb holds the initial length lower bound, used with lb(start)
        // to give the proof-only end = s + l proxy its true lower bound (which
        // is negative when a start can begin far enough before time 0).
        std::vector<Integer> _length_vals;
        std::vector<Integer> _length_lb;
        std::vector<Integer> _length_ub;
        std::vector<Integer> _height_vals;
        std::vector<Integer> _height_ub;
        Integer _capacity_val;
        std::vector<std::size_t> _active_tasks;
        std::vector<Integer> _per_task_t_lo;
        std::vector<Integer> _per_task_t_hi;

        // Filled in by define_proof_model; consumed by install_propagators.
        // Each [task_idx] is indexed by t − _per_task_t_lo[i].
        std::vector<std::vector<innards::ProofFlag>> _before_flags;
        std::vector<std::vector<innards::ProofFlag>> _after_flags;
        std::vector<std::vector<innards::ProofFlag>> _active_flags;
        // Per (variable-height task, t) load contribution contrib = h·active,
        // linearised over cake's per-bit contribution flags v[id][i_t_k][cc]
        // (weight 2^k), so contrib = Σ 2^k·cc_k. Indexed [task][t_idx][bit];
        // empty middle vector for tasks whose height is constant (those use
        // h·active directly in C_t).
        std::vector<std::vector<std::vector<innards::ProofFlag>>> _contrib_flags;
        // For a task whose start AND length both vary, a proof-only end = s + l
        // introduced INSIDE the proof (a conservative extension, with no OPB
        // encoding): cake reifies `after` on s + l directly, so end has no cake
        // counterpart to match. The proof initialiser bit-defines end (via
        // ProofLogger::introduce_bits_of) and emits a per-(i,t) bridge lemma
        // `end ≥ t+1 → after`, which keeps the single-variable-in-end after pin
        // RUP-closable even though `after` is reified on the two-variable s + l.
        // nullopt for all other tasks.
        std::vector<std::optional<innards::ProofOnlySimpleIntegerVariableID>> _end;
        std::map<Integer, innards::ProofLine> _capacity_lines; // t -> proof line for the per-t time-table constraint

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        /**
         * \brief General form: lengths, heights, and capacity may be variables
         * or constants (constants pass through as ConstantIntegerVariableID).
         */
        explicit Cumulative(std::vector<IntegerVariableID> starts, std::vector<IntegerVariableID> lengths, std::vector<IntegerVariableID> heights,
            IntegerVariableID capacity);

        /**
         * \brief Convenience form for the all-constant case (variable starts,
         * constant lengths, heights, and capacity). Delegates to the general
         * constructor.
         */
        explicit Cumulative(std::vector<IntegerVariableID> starts, std::vector<Integer> lengths, std::vector<Integer> heights, Integer capacity);

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
