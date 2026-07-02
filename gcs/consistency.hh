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
     * problem.post(LinearEquality{sum, 5_i, consistency::Tabulated{}});
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
         * \brief Let the solver choose how strongly to propagate, based on the
         * shape of the constraint and the size of the variables' domains.
         *
         * This is a policy rather than a consistency level: constraints that
         * accept it document what it does, and typically it means tabulating
         * (as if consistency::Tabulated had been requested) when the domains
         * involved are small, and falling back on something cheaper when they
         * are not. The choice never changes the constraint's meaning, and
         * never changes how the constraint is encoded for proof logging.
         *
         * \ingroup Consistency
         */
        struct Auto final
        {
        };

        /**
         * \brief Request generalised arc consistency: after propagation, every
         * remaining value in every variable's domain appears in at least one
         * satisfying assignment of the constraint.
         *
         * This tag names a genuine propagation algorithm that achieves the
         * level, which may well be expensive per search node, but whose cost
         * is under the algorithm's control. A constraint that can only reach
         * generalised arc consistency by enumerating every satisfying
         * assignment takes consistency::Tabulated instead, so that the very
         * different cost model is visible in the signature.
         *
         * \ingroup Consistency
         */
        struct GAC final
        {
        };

        /**
         * \brief Request generalised arc consistency achieved by tabulation:
         * every satisfying assignment of the constraint is enumerated up
         * front, and the resulting table is propagated extensionally.
         *
         * This is deliberately a different tag from consistency::GAC, which
         * names a genuine algorithm: a tabulated constraint's set-up work and
         * proof size grow with the product of its variables' domain sizes, so
         * requesting it over wide domains gets very expensive in a way the
         * API should not hide.
         *
         * \ingroup Consistency
         */
        struct Tabulated final
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
         * No constraint accepts it yet: it is here for when the AllDifferent
         * family (whose fastest propagator is exactly this) migrates onto
         * consistency tags in issue #299.
         *
         * \ingroup Consistency
         */
        struct VC final
        {
        };
    }
}

#endif
