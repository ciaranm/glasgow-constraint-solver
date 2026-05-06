#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_TRIGGERS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_TRIGGERS_HH

#include <gcs/innards/literal.hh>
#include <gcs/innards/propagators.hh>

namespace gcs::innards
{
    /**
     * \brief Register the most precise wake-up trigger for the given Literal.
     *
     * - `Equal` / `NotEqual`     -> `triggers.on_change`
     * - `Less` / `GreaterEqual`  -> `triggers.on_bounds`
     * - `TrueLiteral` / `FalseLiteral` -> no-op
     *
     * \ingroup Innards
     */
    auto add_trigger_for(Triggers & triggers, const Literal & lit) -> void;
}

#endif
