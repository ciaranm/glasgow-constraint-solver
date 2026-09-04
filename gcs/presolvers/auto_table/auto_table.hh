#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PRESOLVERS_AUTO_TABLE_AUTO_TABLE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PRESOLVERS_AUTO_TABLE_AUTO_TABLE_HH

#include <gcs/presolver.hh>
#include <gcs/stats.hh>
#include <gcs/variable_id.hh>

#include <cstddef>
#include <memory>
#include <string>
#include <vector>

namespace gcs
{
    /**
     * \brief What the autotabulating presolver did, filled in when it runs.
     *
     * Until #662 this presolver had no block at all, and the only record that
     * it had run was a handful of proof comments --- so with proofs off, which
     * is the configuration anyone measures in, `tuples` was unrecoverable:
     * nothing said whether the table it installed had three entries or three
     * million, and nothing said what finding out had cost. Since the presolver
     * solves a subproblem to exhaustion before search even starts, that is a
     * cost worth being able to see.
     *
     * The presolver allocates one of these whether or not a caller asked for
     * one. \sa AutoTable
     *
     * \ingroup Presolvers
     */
    struct AutoTableStats final : ComponentStats
    {
        /// Whether run() was reached at all. Always true for a block that has
        /// reached Stats::components(), which is registered from inside run();
        /// it is for a caller holding its own handle, whose presolver may never
        /// have been called --- an earlier presolver can refute the problem
        /// first.
        bool ran = false;

        /// Variables tabulated over, which is what the caller asked for and so
        /// the one figure here it already knew.
        std::size_t variables = 0;

        /// Entries in the table that was installed: the number that matters,
        /// and the one that used to exist only inside a proof.
        std::size_t tuples = 0;

        /// Nodes the subproblem search visited to find them. The cost side of
        /// the same trade: a tabulation that took a million nodes to find a
        /// hundred tuples is one a caller would want to know about, and a
        /// presolver that spent that before search started looks, from every
        /// other measurement, exactly like a slow model.
        std::size_t search_nodes = 0;

        /// Whether the table that was installed is large enough for the
        /// compact-table algorithm, which since #809 this presolver's tables can
        /// use. It follows from `tuples` --- the threshold is
        /// innards::ExtensionalCompactTable::min_tuples --- but that threshold
        /// is an innards constant, so a caller holding this block cannot work it
        /// out. Whether the propagator then goes on to *use* the algorithm is a
        /// separate question, decided during search and by measurement; this is
        /// only whether it was offered the choice.
        ///
        /// Last in the block on purpose, so that it gets its own eight bytes
        /// rather than sharing `ran`'s padding: see `field_count` in
        /// solve_test.cc for what depends on that.
        bool compact_table = false;

        [[nodiscard]] virtual auto component_name() const -> std::string override;
        [[nodiscard]] virtual auto summary() const -> std::string override;
        [[nodiscard]] virtual auto entries() const -> std::vector<StatsEntry> override;
    };

    /**
     * \brief Create a Table constraint over the specified variables.
     *
     * \ingroup Presolvers
     */
    class AutoTable : public Presolver
    {
    private:
        const std::vector<IntegerVariableID> _vars;
        std::shared_ptr<AutoTableStats> _stats;

    public:
        /**
         * \brief Construct the presolver, optionally sharing a stats block that
         * outlives the copy Problem takes.
         *
         * A caller that passes none still gets one, and it is still reported.
         */
        explicit AutoTable(const std::vector<IntegerVariableID> & vars, std::shared_ptr<AutoTableStats> stats = nullptr);

        virtual auto run(Problem &, innards::Propagators &, innards::State &, innards::ProofLogger * const) -> bool override;

        /**
         * Create a copy of the presolver, sharing its stats block rather than
         * allocating a fresh one: Problem::add_presolver stores a clone and
         * run() is called on that, so a fresh block here would leave the
         * caller's handle reading zero for ever.
         */
        virtual auto clone() const -> std::unique_ptr<Presolver> override;
    };
}

#endif
