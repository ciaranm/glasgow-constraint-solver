/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROPAGATORS_FWD_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROPAGATORS_FWD_HH

namespace gcs::innards
{
    /**
     * Should a propagator be called again, or is it guaranteed it cannot
     * perform any more inference?
     *
     * \ingroup Innards
     */
    enum class PropagatorState
    {
        Enable,
        DisableUntilBacktrack
    };

    class Propagators;
}

#endif
