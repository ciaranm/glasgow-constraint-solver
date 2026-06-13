#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINT_HH

#include <gcs/innards/proofs/proof_model-fwd.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/innards/s_expr-fwd.hh>
#include <gcs/innards/state-fwd.hh>

#include <functional>
#include <memory>
#include <string>
#include <variant>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#else
#include <fmt/core.h>
#endif

namespace gcs
{
    /**
     * \defgroup Constraints Constraints
     */

    struct CurrentlyUnnamedConstraint final
    {
        [[nodiscard]] auto operator<=>(const CurrentlyUnnamedConstraint &) const = default;
        [[nodiscard]] auto as_string() const -> std::string
        {
            return "unnamed";
        }
    };

    struct NumberedConstraint final
    {
        unsigned long long number;
        [[nodiscard]] auto operator<=>(const NumberedConstraint &) const = default;
        [[nodiscard]] auto as_string() const -> std::string
        {
            return "_" + std::to_string(number);
        }
    };

    struct NamedConstraint final
    {
        std::string name;
        [[nodiscard]] auto operator<=>(const NamedConstraint &) const = default;
        [[nodiscard]] auto as_string() const -> std::string
        {
            return name;
        }
    };

    // The *identity* of a constraint (`_1`, `_2`, or a caller-given name) -- not
    // its type (`abs`, `all_different`, ...). Kept distinct from "name" because
    // both readings of that word kept getting confused.
    using ConstraintID = std::variant<CurrentlyUnnamedConstraint, NumberedConstraint, NamedConstraint>;

    [[nodiscard]] auto as_string(const ConstraintID &) -> std::string;

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

// The following is needed to allow ConstraintID to be used in format strings.
#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
template <>
struct std::formatter<gcs::ConstraintID> : std::formatter<std::string>
{
    auto format(const gcs::ConstraintID & constraint_id, std::format_context & ctx) const
    {
        return std::formatter<std::string>::format(gcs::as_string(constraint_id), ctx);
    }
};
#else
template <>
struct fmt::formatter<gcs::ConstraintID> : fmt::formatter<std::string>
{
    auto format(const gcs::ConstraintID & constraint_id, fmt::format_context & ctx) const
    {
        return fmt::formatter<std::string>::format(gcs::as_string(constraint_id), ctx);
    }
};
#endif

// Lets ConstraintID be used as a key in unordered containers (the weighting
// state map, the dense-index map in Propagators). Equality on the variant is
// structural; hashing its string form agrees with that.
template <>
struct std::hash<gcs::ConstraintID>
{
    [[nodiscard]] auto operator()(const gcs::ConstraintID & constraint_id) const -> std::size_t
    {
        return std::hash<std::string>{}(gcs::as_string(constraint_id));
    }
};

#endif
