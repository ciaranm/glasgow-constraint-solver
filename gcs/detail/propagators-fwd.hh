/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROPAGATORS_FWD_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROPAGATORS_FWD_HH 1

namespace gcs
{
    enum class PropagatorState
    {
        Enable,
        DisableUntilBacktrack
    };

    class Propagators;
}

#endif
