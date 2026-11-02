#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_OBJECTIVE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_OBJECTIVE_HH

#include <gcs/variable_id.hh>

namespace gcs
{
    /**
     * \brief Whether an Objective is to be minimised or maximised.
     *
     * \ingroup Core
     */
    enum class ObjectiveDirection
    {
        Minimise,
        Maximise
    };

    /**
     * \brief An objective, as posted by Problem::minimise() or
     * Problem::maximise().
     *
     * The variable and direction are kept exactly as given, so that
     * `maximise(x + 2_i)` is not the same objective as `minimise(-x - 2_i)`,
     * even though the two have the same optimal solutions: what the proof
     * files and the solver's output report is the posted objective's value.
     *
     * \ingroup Core
     */
    struct Objective final
    {
        IntegerVariableID variable;
        ObjectiveDirection direction;
    };
}

#endif
