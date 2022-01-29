/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_EXTENSIONAL_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_EXTENSIONAL_HH 1

#include <gcs/integer.hh>
#include <gcs/propagators-fwd.hh>
#include <gcs/state-fwd.hh>
#include <gcs/variable_id.hh>

#include <utility>
#include <vector>

namespace gcs
{
    struct ExtensionalData
    {
        IntegerVariableID selector;
        std::vector<IntegerVariableID> vars;
        std::vector<std::vector<Integer>> tuples;
    };

    auto propagate_extensional(const ExtensionalData &, State &) -> std::pair<Inference, PropagatorState>;
}

#endif
