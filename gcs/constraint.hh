/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINT_HH

#include <gcs/innards/propagators-fwd.hh>
#include <gcs/innards/state-fwd.hh>

#include <string>

namespace gcs
{
    /**
     * \defgroup Constraints Constraints
     */

    /**
     * \brief Subclasses of Constraint give a high level way of defining
     * constraints. See \ref Constraints for a list of available constraints.
     *
     * A Constraint subclass instance should only be used by passing it to
     * Problem::post(), and it can only be used in this way once: an instance
     * may modify, move, or destroy its arguments upon use.  Internally, Problem
     * will call Constraint::install(), which in turn defines zero or more
     * propagators that do the actual work.
     *
     * \ingroup Core
     */
    class [[nodiscard]] Constraint
    {
    public:
        virtual ~Constraint() = 0;

        /**
         * For proof logging, give a short textual description of the constraint
         * that will be turned into a comment in the OPB file.
         */
        virtual auto describe_for_proof() -> std::string = 0;

        /**
         * Called by Problem to install the constraint. A Constraint is expected
         * to define zero or more propagators, and to provide a description of
         * its meaning for proof logging.
         */
        virtual auto install(innards::Propagators &, const innards::State &) && -> void = 0;
    };
}

#endif
