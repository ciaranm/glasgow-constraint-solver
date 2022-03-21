/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_EXTENSIONAL_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_EXTENSIONAL_HH

#include <gcs/integer.hh>

#include <variant>
#include <vector>

namespace gcs
{
    /**
     * \defgroup Extensional Extensional constraints
     */

    /**
     * \brief Simple tuples that are just Integers.
     *
     * \sa gcs::innards::propagate_extensional()
     * \sa gcs::WildcardTuples
     * \sa gcs::Table
     * \ingroup Extensional
     */
    using SimpleTuples = std::vector<std::vector<Integer>>;

    /**
     * \brief Wildcard for innards::ExtensionalData.
     *
     * \sa IntegerOrWildcard
     * \sa WildcardTuples
     * \sa ExtensionalData
     * \sa gcs::Table
     * \ingroup Extensional
     */
    struct Wildcard
    {
    };

    /**
     * \brief A tuple entry which is either an Integer or a wildcard.
     *
     * \sa Wildcard
     * \sa WildcardTuples
     * \sa ExtensionalData
     * \sa gcs::Table
     * \ingroup Extensional
     */
    using IntegerOrWildcard = std::variant<Integer, Wildcard>;

    /**
     * \brief Tuples that can contain wildcards.
     *
     * \sa gcs::innards::propagate_extensional()
     * \sa gcs::SimpleTuples
     * \sa gcs::Table
     * \ingroup Extensional
     */
    using WildcardTuples = std::vector<std::vector<IntegerOrWildcard>>;

    /**
     * \brief Tuples for extensional constraints.
     *
     * \sa ExtensionalData
     * \sa gcs::innards::propagate_extensional()
     * \sa gcs::Table
     * \ingroup Extensional
     */
    using ExtensionalTuples = std::variant<SimpleTuples, WildcardTuples>;
}

#endif
