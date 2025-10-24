#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_REASON_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_REASON_HH

#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/reification.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/variable_id.hh>

#include <functional>
#include <vector>

namespace gcs::innards
{
    using Reason = std::vector<ProofLiteralOrFlag>;
    using ReasonFunction = std::function<auto()->Reason>;

    [[nodiscard]] auto generic_reason(const State & state, const std::vector<IntegerVariableID> & vars) -> ReasonFunction;

    [[nodiscard]] auto singleton_reason(const IntegerVariableCondition & lit) -> ReasonFunction;
}

#endif
