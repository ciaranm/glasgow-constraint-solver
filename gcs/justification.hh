/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_JUSTIFICATION_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_JUSTIFICATION_HH 1

#include <gcs/proof-fwd.hh>

#include <functional>
#include <variant>

namespace gcs
{
    struct Guess
    {
    };

    struct JustifyExplicitly
    {
        std::function<auto (Proof &) -> void> add_proof_steps;
    };

    struct JustifyUsingRUP
    {
    };

    struct JustifyUsingAssertion
    {
    };

    struct NoJustificationNeeded
    {
    };

    using Justification = std::variant<Guess, JustifyUsingRUP, JustifyUsingAssertion, JustifyExplicitly, NoJustificationNeeded>;
}

#endif
