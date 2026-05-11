#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINT_HH

#include <gcs/innards/proofs/proof_model-fwd.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/innards/state-fwd.hh>

#include <format>
#include <memory>
#include <string>
#include <variant>

namespace gcs
{
    /**
     * \defgroup Constraints Constraints
     */

    struct CurrentlyUnnamedConstraint final
    {
        auto as_string() const -> std::string { return "unnamed"; }
    };

    struct NumberedConstraint final
    {
        unsigned long long number;

        // Claude (web) says this is a good idea for comparisons.
        // Do we need comparisons? (C++20 spaceship operator)
        auto operator<=>(const NumberedConstraint &) const = default;
        auto as_string() const -> std::string { return "C" + std::to_string(number); }  // TODO: change "C" to "_" at some point before merge
    };

    struct NamedConstraint final
    {
        std::string name;
        auto operator<=>(const NamedConstraint &) const = default;
        auto as_string() const -> std::string { return name; }
    };

    using ConstraintName = std::variant<CurrentlyUnnamedConstraint, NumberedConstraint, NamedConstraint>;

    auto as_string(const ConstraintName &) -> std::string;

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
        ConstraintName _name;
        Constraint() : _name(CurrentlyUnnamedConstraint{}) {};
        explicit Constraint(ConstraintName name) : _name(std::move(name)) {};
        virtual auto define_proof_model(innards::ProofModel &) -> void {};
        virtual auto install_propagators(innards::Propagators &) -> void {};
        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool
        {
            return true;
        };

    public:
        virtual ~Constraint() = 0;
        auto name() const -> const ConstraintName & { return _name; }
        auto set_name(ConstraintName name) -> void { _name = std::move(name); }
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
        [[nodiscard]] virtual auto s_exprify(const innards::ProofModel * const) const -> std::string = 0;
    };
}

// The following is needed to allow ConstraintName to be used in format strings.
// We do this quite a lot in s_exprify().  If we didn't do this, we'd have to write
// `format("{}", as_string(_name))` everywhere instead of just `format("{}", _name)`.
// It's comfort over clarity.  What's the best option?
#if defined(__cpp_lib_format)
template <>
struct std::formatter<gcs::ConstraintName> : std::formatter<std::string>
{
    auto format(const gcs::ConstraintName & name, std::format_context & ctx) const
    {
        return std::formatter<std::string>::format(gcs::as_string(name), ctx);
    }
};
#else
template <>
struct fmt::formatter<gcs::ConstraintName> : fmt::formatter<std::string>
{
    auto format(const gcs::ConstraintName & name, fmt::format_context & ctx) const
    {
        return fmt::formatter<std::string>::format(gcs::as_string(name), ctx);
    }
};
#endif

#endif
