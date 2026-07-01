#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSISTENCY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSISTENCY_HH

namespace gcs
{
    /**
     * \defgroup Consistency Selecting a consistency level or propagation algorithm
     *
     * Some constraints can achieve more than one level of consistency, usually
     * with stronger levels costing more per search node. Such a constraint's
     * constructor takes a `std::variant` over tag types naming exactly the
     * levels it supports, defaulted to a sensible choice, for example
     *
     * \code{.cc}
     * problem.post(LinearEquality{sum, 5_i, consistency::GAC{}});
     * \endcode
     *
     * Requesting a level a constraint does not support is a compile-time
     * error: the constructor signature is the documentation. These tags
     * select propagation strength only; they never change the constraint's
     * meaning, and they never change how the constraint is encoded for proof
     * logging.
     */

    namespace consistency
    {
        /**
         * \brief Request generalised arc consistency: after propagation, every
         * remaining value in every variable's domain appears in at least one
         * satisfying assignment of the constraint.
         *
         * This is the strongest level, and can be very expensive for large
         * domains.
         *
         * \ingroup Consistency
         */
        struct GAC final
        {
        };

        /**
         * \brief Request bounds consistency: after propagation, the lower and
         * upper bound of every variable's domain appear in at least one
         * bounds-satisfying assignment of the constraint.
         *
         * \ingroup Consistency
         */
        struct BC final
        {
        };

        /**
         * \brief Request value consistency: after propagation, each variable
         * that has been given a fixed value has had its immediate consequences
         * enforced, but no stronger reasoning is carried out.
         *
         * This is the weakest level, and usually the cheapest per search node.
         *
         * \ingroup Consistency
         */
        struct VC final
        {
        };
    }
}

#endif
