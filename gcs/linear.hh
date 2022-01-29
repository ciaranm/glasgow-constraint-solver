/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_LINEAR_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_LINEAR_HH 1

#include <gcs/integer.hh>
#include <gcs/proof-fwd.hh>
#include <gcs/propagators-fwd.hh>
#include <gcs/state-fwd.hh>
#include <gcs/variable_id.hh>

#include <optional>
#include <utility>
#include <vector>

namespace gcs
{
    using CoefficientAndVariable = std::pair<Integer, IntegerVariableID>;
    using Linear = std::vector<CoefficientAndVariable>;

    auto sanitise_linear(Linear &) -> void;

    auto propagate_linear(const Linear &, Integer, State &, bool equality,
        std::optional<ProofLine> proof_line) -> std::pair<Inference, PropagatorState>;
}

#endif
