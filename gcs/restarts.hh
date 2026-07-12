#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_RESTARTS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_RESTARTS_HH

namespace gcs
{
    /**
     * \brief A restart schedule: a growing sequence of conflict cutoffs for
     * gcs::solve_with().
     *
     * When a SolveCallbacks carries one, search runs as a loop of restarts ---
     * each restart explores until it has seen the current cutoff's worth of
     * conflicts (domain wipeouts), then abandons the tree and begins again from
     * the root, with the cutoff advanced to the next term of the sequence and any
     * weighting decay applied. Weights (and, in optimisation, the incumbent
     * bound) persist across restarts, so a later run searches differently.
     *
     * The only policy provided is Luby (Knuth's reluctant doubling: the sequence
     * 1, 1, 2, 1, 1, 2, 4, ... times a scale), whose growing-but-occasionally-
     * small cutoffs eventually exceed any tree's size, so a final run completes
     * and the search terminates. The scale is a tunable isolated behind a default
     * (see issue #315), not a design input.
     *
     * \warning Without recorded nogoods a restart re-explores --- and so
     * re-finds --- solutions, so a restart schedule is only sound for finding one
     * solution or for optimising. Combining it with all-solution enumeration is
     * rejected at runtime (gcs::solve_with throws UnimplementedException).
     *
     * \ingroup Core
     * \sa gcs::SolveCallbacks
     */
    class RestartSchedule final
    {
    private:
        explicit RestartSchedule(unsigned long long scale);

        unsigned long long _scale;
        unsigned long long _index; // 1-based position in the Luby sequence

    public:
        /**
         * \brief A Luby schedule: cutoff i is luby(i) * \p scale conflicts.
         */
        [[nodiscard]] static auto luby(unsigned long long scale = 100ULL) -> RestartSchedule;

        /**
         * \brief The current cutoff, in conflicts since the last restart.
         */
        [[nodiscard]] auto current_cutoff() const -> unsigned long long;

        /**
         * \brief Advance to the next cutoff in the sequence; call once at each
         * restart boundary.
         */
        auto advance() -> void;
    };
}

#endif
