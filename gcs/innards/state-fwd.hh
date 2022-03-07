/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATE_FWD_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATE_FWD_HH

namespace gcs::innards
{
    class State;

    /**
     * Has a propagator made any changes?
     *
     * \ingroup Innards
     */
    enum class Inference
    {
        NoChange,
        Change,
        Contradiction
    };

    /**
     * How has a variable's state changed? Must be kept in order of importance.
     *
     * \ingroup Innards
     */
    enum class HowChanged
    {
        Dummy = -1,
        InteriorValuesChanged = 0,
        BoundsChanged = 1,
        Instantiated = 2
    };
}

#endif
