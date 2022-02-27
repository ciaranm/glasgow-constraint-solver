/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINT_HH

#include <gcs/detail/propagators-fwd.hh>
#include <gcs/detail/state-fwd.hh>

#include <string>

namespace gcs
{
    class [[nodiscard]] Constraint
    {
    public:
        virtual ~Constraint() = 0;

        virtual auto describe_for_proof() -> std::string = 0;
        virtual auto install(detail::Propagators &, const detail::State &) && -> void = 0;
    };
}

#endif
