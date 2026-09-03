#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_EXTENSIONAL_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_EXTENSIONAL_HH

#include <gcs/array_param.hh>
#include <gcs/integer.hh>

#include <memory>
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
     * \brief SimpleTuples but shared data (must be immutable).
     * \sa gcs::innards::propagate_extensional()
     * \sa gcs::WildcardTuples
     * \sa gcs::Table
     * \ingroup Extensional
     */
    using SharedSimpleTuples = std::shared_ptr<const SimpleTuples>;

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
     * \brief SimpleTuples but shared data (must be immutable).
     * \sa gcs::innards::propagate_extensional()
     * \sa gcs::WildcardTuples
     * \sa gcs::Table
     * \ingroup Extensional
     */
    using SharedWildcardTuples = std::shared_ptr<const WildcardTuples>;

    /**
     * \brief Tuples for extensional constraints.
     *
     * \sa ExtensionalData
     * \sa gcs::innards::propagate_extensional()
     * \sa gcs::Table
     * \ingroup Extensional
     */
    using ExtensionalTuples = std::variant<ArrayParam<SimpleTuples>, ArrayParam<WildcardTuples>>;

    /**
     * \brief Tags for the algorithms gcs::Table can propagate with.
     *
     * \ingroup Extensional
     */
    namespace table
    {
        /**
         * \brief Watch the table for a while, then switch to table::CompactTable
         * if and only if this instance looks like one that will pay for it:
         * enough wakes to amortise building the masks, a live set big enough that
         * a call does real work, and a live set dense enough in its words that a
         * bitset is the right shape for it.
         *
         * The default, and the only setting without a significant regression on
         * this project's suite -- it is within 2% of the better of the other two
         * everywhere except `srch_bin_d10_n20_s2`, where it is 4% behind.
         *
         * \ingroup Extensional
         */
        struct Auto final
        {
        };

        /**
         * \brief Keep the still-selectable tuples in a sparse set, and re-test
         * each of them against the current domains on every wake. Costs what is
         * live.
         *
         * \ingroup Extensional
         */
        struct LiveSet final
        {
        };

        /**
         * \brief Keep them in a bitset with a support mask per (position, value),
         * and take out the tuples that used a value as it goes. Costs what
         * changed, which on a large table is far less -- but it builds and holds
         * the masks, so a table that is woken only a handful of times pays for
         * something it never uses.
         *
         * Forced from the first call, where table::Auto waits and then decides:
         * this is the setting to benchmark Auto against, not the one to ship.
         *
         * \ingroup Extensional
         */
        struct CompactTable final
        {
        };
    }

    /**
     * \brief The propagation algorithms supported by gcs::Table: table::Auto (the
     * default), table::LiveSet or table::CompactTable. Requesting anything else is
     * a compile-time error, and the choice never changes the constraint's meaning,
     * its search tree, or its proof -- all three make exactly the same inferences
     * in the same order.
     *
     * \ingroup Extensional
     */
    using TableAlgorithm = std::variant<table::Auto, table::LiveSet, table::CompactTable>;
}

#endif
