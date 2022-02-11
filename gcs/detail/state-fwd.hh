/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATE_FWD_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATE_FWD_HH

namespace gcs
{
    class State;

    enum class Inference
    {
        NoChange,
        Change,
        Contradiction
    };

    // must be in order of propagation importance
    enum class HowChanged
    {
        Dummy = -1,
        InteriorValuesChanged = 0,
        BoundsChanged = 1,
        Instantiated = 2
    };
}

#endif
