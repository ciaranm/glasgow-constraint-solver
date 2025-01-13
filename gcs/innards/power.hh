#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_POWER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_POWER_HH

#include <gcs/integer.hh>

namespace gcs::innards
{
    [[nodiscard]] auto power2(Integer i) -> Integer;
}

#endif
