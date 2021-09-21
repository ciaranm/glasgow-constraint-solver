/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATE_FWD_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_STATE_FWD_HH 1

namespace gcs
{
    class State;

    enum class Inference
    {
        NoChange,
        Change,
        Contradiction
    };

}

#endif
