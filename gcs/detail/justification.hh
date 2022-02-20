/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_JUSTIFICATION_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_JUSTIFICATION_HH

#include <gcs/detail/proof-fwd.hh>

#ifdef GCS_TRACK_ALL_PROPAGATIONS
#  include <experimental/source_location>
#endif

#include <functional>
#include <variant>
#include <vector>

namespace gcs
{
    using ExplicitJustificationFunction = std::function<auto(Proof &, std::vector<ProofLine> &)->void>;

    struct Guess
    {
    };

    struct JustifyExplicitly
    {
        ExplicitJustificationFunction add_proof_steps;
    };

    struct JustifyUsingRUP
    {
#ifdef GCS_TRACK_ALL_PROPAGATIONS
        std::experimental::source_location where;

        explicit JustifyUsingRUP(const std::experimental::source_location & w = std::experimental::source_location::current()) :
            where(w)
        {
        }
#else
#endif
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
