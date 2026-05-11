#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CUMULATIVE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CUMULATIVE_HH

#include <gcs/constraint.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <cstddef>
#include <vector>

namespace gcs
{
    /**
     * \brief Cumulative constraint, basic case: tasks with variable origins
     * and constant durations, demands, and capacity. At every time point the
     * sum of demands of currently-active tasks must not exceed the capacity.
     *
     * A task <em>i</em> is active at time <em>t</em> iff
     * <em>starts[i] &le; t &lt; starts[i] + lengths[i]</em>.
     *
     * Stage-1 propagation is purely a feasibility checker: it fires only when
     * every start has been instantiated and reports a contradiction if the
     * load profile ever exceeds the capacity. Stronger propagation
     * (time-table consistency, edge-finding, ...) is left for future work.
     *
     * \ingroup Constraints
     */
    class Cumulative : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _starts;
        std::vector<Integer> _lengths;
        std::vector<Integer> _heights;
        Integer _capacity;
        std::vector<std::size_t> _active_tasks;
        std::vector<Integer> _per_task_t_lo;
        std::vector<Integer> _per_task_t_hi;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit Cumulative(std::vector<IntegerVariableID> starts,
            std::vector<Integer> lengths,
            std::vector<Integer> heights,
            Integer capacity);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const innards::ProofModel * const) const -> std::string override;
    };
}

#endif
