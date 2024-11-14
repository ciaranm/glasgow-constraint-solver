#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATE_FWD_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATE_FWD_HH

namespace gcs::innards
{
    class State;

    /**
     * Has a propagator made any changes?
     *
     * Values must be kept in order of changinesss.
     *
     * \ingroup Innards
     */
    enum class Inference
    {
        NoChange,
        BoundsChanged,
        InteriorValuesChanged,
        Instantiated,
        Contradiction
    };
}

#endif
