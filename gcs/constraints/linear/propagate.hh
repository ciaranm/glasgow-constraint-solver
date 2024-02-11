#include <gcs/constraints/linear/utils.hh>
#include <gcs/expression.hh>
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
    auto propagate_linear(const SumOf<Weighted<SimpleIntegerVariableID>> &, Integer, State &,
        ProofLogger * const logger, bool equality,
        const std::optional<ProofLine> & proof_line) -> std::pair<Inference, PropagatorState>;

    /**
     * \brief Propagate a simple sum equality or inequality.
     *
     * \ingroup Innards
     */
    auto propagate_sum(const SumOf<PositiveOrNegative<SimpleIntegerVariableID>> &, Integer, State &,
        ProofLogger * const logger, bool equality,
        const std::optional<ProofLine> & proof_line) -> std::pair<Inference, PropagatorState>;

    /**
     * \brief Propagate an all-positive sum equality or inequality.
     *
     * \ingroup Innards
     */
    auto propagate_sum_all_positive(const SumOf<SimpleIntegerVariableID> &, Integer, State &,
        ProofLogger * const logger, bool equality,
        const std::optional<ProofLine> & proof_line) -> std::pair<Inference, PropagatorState>;
}
