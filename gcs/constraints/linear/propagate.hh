#include <gcs/constraints/linear/utils.hh>
#include <gcs/expression.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/innards/state-fwd.hh>

#include <optional>

namespace gcs::innards
{
    /**
     * \brief Propagate a linear equality or inequality.
     *
     * \ingroup Innards
     */
    auto propagate_linear(const auto & terms, Integer, State &,
        ProofLogger * const logger, bool equality,
        const std::optional<ProofLine> & proof_line,
        const std::optional<Literal> & add_to_reason) -> std::pair<Inference, PropagatorState>;

    /**
     * \brief Propagate a not-equals
     *
     * \ingroup Innards
     */
    auto propagate_linear_not_equals(const auto & terms, Integer, State &,
        ProofLogger * const logger,
        const std::vector<IntegerVariableID> & all_vars_for_reason) -> std::pair<Inference, PropagatorState>;
}
