#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_REIFICATION_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_REIFICATION_HH

#include <gcs/variable_condition.hh>
#include <gcs/variant.hh>

#include <variant>

namespace gcs
{
    namespace reif
    {
        struct MustHold
        {
        };

        struct MustNotHold
        {
        };

        struct If
        {
            IntegerVariableCondition cond;
        };

        struct NotIf
        {
            IntegerVariableCondition cond;
        };

        struct Iff
        {
            IntegerVariableCondition cond;
        };
    }

    using ReificationCondition = gcs::variant<
        reif::MustHold,
        reif::MustNotHold,
        reif::If,
        reif::NotIf,
        reif::Iff>;
}

#endif
