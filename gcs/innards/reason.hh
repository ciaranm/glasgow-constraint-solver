#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_REASON_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_REASON_HH

#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/reification.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/variable_id.hh>

#include <functional>
#include <optional>
#include <vector>

namespace gcs::innards
{
    using Reason = std::vector<ProofLiteralOrFlag>;
    using ReasonFunction = std::function<auto()->Reason>;

    /**
     * \brief Build a reason recording every value in each variable's domain
     * (lower bound, upper bound, and any holes). If `extra_lit` is supplied
     * it is appended too — handy for reified propagators that want the
     * reification literal in the reason alongside the variable facts.
     */
    [[nodiscard]] auto generic_reason(const State & state, const std::vector<IntegerVariableID> & vars,
        const std::optional<Literal> & extra_lit = std::nullopt) -> ReasonFunction;

    /**
     * \brief Like generic_reason but records only the lower and upper bounds of each
     * variable, omitting any holes in the domain.
     *
     * Suitable for propagators whose inferences depend only on bounds (every
     * fact consulted is a comparison against `lo` or `hi`). Produces smaller
     * reasons than generic_reason when domains are wide. The optional
     * `extra_lit` is appended to the reason when present.
     */
    [[nodiscard]] auto bounds_reason(const State & state, const std::vector<IntegerVariableID> & vars,
        const std::optional<Literal> & extra_lit = std::nullopt) -> ReasonFunction;

    [[nodiscard]] auto singleton_reason(const ProofLiteralOrFlag & lit) -> ReasonFunction;
}

#endif
