#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINT_HH

#include <gcs/constraint_id.hh>
#include <gcs/innards/proofs/proof_model-fwd.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/innards/s_expr-fwd.hh>
#include <gcs/innards/state-fwd.hh>

#include <memory>
#include <string>
#include <variant>
#include <version>

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
    protected:
        ConstraintID _constraint_id;
        Constraint() : _constraint_id(CurrentlyUnnamedConstraint{}) {};
        explicit Constraint(ConstraintID constraint_id) : _constraint_id(std::move(constraint_id)) {};
        virtual auto define_proof_model(innards::ProofModel &) -> void {};
        virtual auto install_propagators(innards::Propagators &) -> void {};
        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool
        {
            return true;
        };

    public:
        virtual ~Constraint() = 0;

        /**
         * \brief The constraint's identity --- `_1`, `_2`, or a caller-given
         * name --- as set by Problem::post() / Problem::post_named(). This is the
         * identity, not the type (e.g. `abs`); see ConstraintID.
         */
        [[nodiscard]] auto constraint_id() const -> const ConstraintID &
        {
            return _constraint_id;
        }

        /**
         * \brief Set the constraint's identity. Called internally by Problem when
         * the constraint is posted (and when its install-time clone is made), so
         * its proof labels match the name written to the `.scp`.
         */
        auto set_constraint_id(ConstraintID constraint_id) -> void
        {
            _constraint_id = std::move(constraint_id);
        }
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
         * Return the constraint's `.scp` entry as an s-expression term: the
         * list `(name op args...)`. This is the preferred representation --
         * routing the writer through it (see innards::write_scp) means the
         * stringification happens once, centrally, and the structured term can
         * be compared against a parsed `.scp` line directly.
         *
         * A constraint must override **exactly one** of s_expr() (preferred) or
         * the legacy s_exprify(): by default s_expr() parses s_exprify()'s
         * string and s_exprify() prints s_expr(), so overriding neither would
         * recurse. New constraints should override s_expr(); the remaining
         * legacy s_exprify() overrides are being migrated across (see
         * dev_docs/scp_s_expr_migration.md), after which s_exprify() goes away.
         */
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr;

        /**
         * Legacy string form: the body of s_expr() *without* the enclosing
         * parentheses (the historical `Constraint::s_exprify` contract). \see
         * s_expr.
         */
        [[nodiscard]] virtual auto s_exprify(const innards::ProofModel * const) const -> std::string;
    };
}

#endif
