#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_LITERAL_UTILS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_LITERAL_UTILS_HH

#include <gcs/literal.hh>

#include <optional>
#include <utility>
#include <vector>

namespace gcs::innards
{
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
}

#endif
