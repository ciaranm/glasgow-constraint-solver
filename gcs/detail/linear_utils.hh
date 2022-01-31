/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_DETAIL_LINEAR_UTILS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_DETAIL_LINEAR_UTILS_HH 1

#include <gcs/detail/propagators-fwd.hh>
#include <gcs/detail/state-fwd.hh>
#include <gcs/linear.hh>
#include <gcs/proof-fwd.hh>

#include <optional>
#include <vector>

namespace gcs
{
    auto sanitise_linear(Linear &) -> void;

    auto propagate_linear(const Linear &, Integer, State &, bool equality,
        std::optional<ProofLine> proof_line) -> std::pair<Inference, PropagatorState>;
}

#endif
