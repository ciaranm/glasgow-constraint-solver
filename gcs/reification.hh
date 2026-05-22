#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_REIFICATION_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_REIFICATION_HH

#include <gcs/variable_condition.hh>

#include <boost/variant2/variant.hpp>

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

    using ReificationCondition = boost::variant2::variant<
        reif::MustHold,
        reif::MustNotHold,
        reif::If,
        reif::NotIf,
        reif::Iff>;
}

#endif
