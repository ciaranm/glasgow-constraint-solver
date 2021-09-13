/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINT_HH 1

#include <functional>
#include <string>

namespace gcs
{
    class LowLevelConstraintStore;
    class State;

    class Constraint
    {
        public:
            virtual ~Constraint() = 0;

            virtual auto describe_for_proof() -> std::string = 0;
            virtual auto convert_to_low_level(LowLevelConstraintStore &, const State &) && -> void = 0;
    };
}

#endif
