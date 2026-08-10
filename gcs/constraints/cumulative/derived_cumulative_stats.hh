#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CUMULATIVE_DERIVED_CUMULATIVE_STATS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_CUMULATIVE_DERIVED_CUMULATIVE_STATS_HH

#include <gcs/stats.hh>

#include <cstddef>
#include <string>
#include <vector>

namespace gcs
{
    /**
     * \brief What install_derived_cumulative() did, summed over every derived
     * Cumulative a caller installed.
     *
     * Not a ComponentStats of its own, and deliberately: a derived Cumulative
     * is installed once per donor, so one component entry per derived
     * constraint would be noise where one aggregate is what a reader wants. A
     * caller keeps one of these inside its own block --- see
     * CumulativeStrengtheningStats::derived --- and hands
     * DerivedCumulativeSpec::stats a share of it, so every install adds to the
     * same figures.
     *
     * \ingroup Innards
     */
    struct DerivedCumulativeStats final
    {
        /// Derived constraints installed: one per successful call.
        std::size_t constraints = 0;

        /// Donors those constraints took their capacity rows from, summed. A
        /// derived constraint over several resources names more than one.
        std::size_t donors = 0;

        /// Per-time capacity rows derived, summed. Zero with proofs off, there
        /// being no rows to derive: it is a measure of what the certificate
        /// cost, not of what the constraint says.
        std::size_t capacity_rows = 0;

        /// Makespan lower bounds actually pushed. Only a spec that asked for a
        /// makespan can contribute, and only where the energy argument reached
        /// a bound at all, so this is the count that says the argument fired
        /// rather than that it was asked for.
        std::size_t makespan_bounds_posted = 0;

        /**
         * \brief Append these figures to a flat view, under `prefix`.
         *
         * For the enclosing block's ComponentStats::entries(), which is where
         * these reach a caller: they are part of that block's flat view rather
         * than a view of their own.
         */
        auto add_entries_to(std::vector<StatsEntry> & entries, const std::string & prefix) const -> void;
    };
}

#endif
