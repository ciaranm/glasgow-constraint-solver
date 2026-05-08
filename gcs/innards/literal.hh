#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_LITERAL_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_LITERAL_HH

#include <gcs/integer.hh>
#include <gcs/variable_condition.hh>
#include <gcs/variable_id.hh>

#include <gch/small_vector.hpp>

#include <optional>
#include <string>
#include <variant>
#include <vector>

namespace gcs::innards
{
    /**
     * \defgroup Literals Literal expressions
     */

    /**
     * \brief A Literal that is always true.
     *
     * \ingroup Literals
     */
    struct TrueLiteral final
    {
        /**
         * \brief Comparison, no defined meaning but allows for sorting etc.
         */
        [[nodiscard]] auto operator<=>(const TrueLiteral &) const = default;
    };

    /**
     * \brief A Literal that is always false.
     *
     * \ingroup Literals
     */
    struct FalseLiteral final
    {
        /**
         * \brief Comparison, no defined meaning but allows for sorting etc.
         */
        [[nodiscard]] constexpr auto operator<=>(const FalseLiteral &) const = default;
    };

    /**
     * \brief A Literal can be an IntegerVariableCondition, or a TrueLiteral or
     * FalseLiteral.
     *
     * \ingroup Literals
     */
    using Literal = std::variant<IntegerVariableCondition, TrueLiteral, FalseLiteral>;

    [[nodiscard]] auto operator!(const TrueLiteral &) -> FalseLiteral;

    [[nodiscard]] auto operator!(const FalseLiteral &) -> TrueLiteral;

    /**
     * \brief Negate a Literal.
     *
     * Gives the literal with the opposite meaning, for example equals becomes
     * not equal, and TrueLiteral becomes a FalseLiteral.
     *
     * \ingroup Literals
     */
    [[nodiscard]] auto operator!(const Literal &) -> Literal;

    /**
     * \brief A small vector of Literal values.
     *
     * Used for CNF clause emission and proof model add_constraint, where
     * clauses are usually short (a handful of literals). Inline capacity 2
     * keeps the common cases off the heap; longer clauses still work via
     * fallback heap allocation.
     *
     * \ingroup Literals
     */
    using Literals = gch::small_vector<Literal, 2>;

    /**
     * \brief Returns whether a Literal is either a TrueLiteral, a FalseLiteral,
     * or a LiteralFromIntegerVariable on a constant that must be either true or
     * false.
     *
     * \sa gcs::innards::is_literally_true
     * \sa gcs::innards::is_literally_false
     * \ingroup Innards
     */
    [[nodiscard]] auto is_literally_true_or_false(const Literal &) -> std::optional<bool>;

    /**
     * \brief Returns whether a Literal is either a TrueLiteral, or a
     * LiteralFromIntegerVariable on a constant that must be true.
     *
     * \sa gcs::innards::is_literally_true_or_false
     * \sa gcs::innards::is_literally_false
     * \ingroup Innards
     */
    [[nodiscard]] auto is_literally_true(const Literal &) -> bool;

    /**
     * \brief Returns whether a Literal is either a FalseLiteral, or a
     * LiteralFromIntegerVariable on a constant that must be false.
     *
     * \sa gcs::innards::is_literally_true_or_false
     * \sa gcs::innards::is_literally_true
     * \ingroup Innards
     */
    [[nodiscard]] auto is_literally_false(const Literal &) -> bool;

    /**
     * \brief Turn a Literal into a semi-readable string for debugging.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto debug_string(const Literal &) -> std::string;

    /**
     * \brief Turn a Literals into a semi-readable string for debugging.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto debug_string(const Literals &) -> std::string;
}

#endif
