#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATE_FWD_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATE_FWD_HH

namespace gcs::innards
{
    class State;

    /**
     * How has a variable's state changed? Must be kept in order of importance.
     *
     * \ingroup Innards
     */
    enum class HowChanged
    {
        Unchanged = -1,
        InteriorValuesChanged = 0,
        BoundsChanged = 1,
        Instantiated = 2,
        Contradiction = 3
    };
}

#endif
