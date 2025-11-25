#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINT_HH

#include <gcs/innards/proofs/proof_model-fwd.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/innards/state-fwd.hh>

#include <memory>
#include <optional>
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
         * Called internally to install the constraint. A Constraint is expected
         * to define zero or more propagators, and to provide a description of
         * its meaning for proof logging. This is a destructive operation which
         * can only be called once, and after calling it neither install() nor
         * clone() may be called on this instance.
         */
        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void = 0;

        /**
         * Create a copy of the constraint. To be used internally.
         */
        [[nodiscard]] virtual auto clone() const -> std::unique_ptr<Constraint> = 0;

        /**
         * Return an s-expr representation of the constraint. To be used internally.
         */
        [[nodiscard]] virtual auto s_exprify(const innards::ProofModel * const) const -> std::string;
    };
}

#endif
