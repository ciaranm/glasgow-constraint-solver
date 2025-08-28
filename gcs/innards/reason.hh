#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_REASON_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_REASON_HH

#include <gcs/innards/literal.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/variable_id.hh>

#include <functional>
#include <vector>

namespace gcs::innards
{
    using Reason = std::function<auto()->Literals>;

    [[nodiscard]] auto generic_reason(const State & state, const std::vector<IntegerVariableID> & vars) -> Reason;

    [[nodiscard]] auto singleton_reason( const IntegerVariableCondition & lit) -> Reason;
}

#endif
