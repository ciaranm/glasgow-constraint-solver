#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PRESOLVERS_INNARDS_CUMULATIVE_STRENGTHENING_MUTATIONS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PRESOLVERS_INNARDS_CUMULATIVE_STRENGTHENING_MUTATIONS_HH

#include <variant>

/**
 * \file
 *
 * Deliberate corruptions of `CumulativeStrengthening`'s proof steps, which exist so that a test can
 * show the honest derivation is tight to what it claims. They live here, in the
 * innards, rather than beside the presolver they corrupt: the header a user
 * includes to run it should not also advertise a way to make the solver emit
 * deliberately wrong proofs. Issue #669; see
 * gcs/constraints/innards/cumulative_mutations.hh for why compiling them out of
 * release builds was rejected.
 */

namespace gcs::innards
{
    /**
     * \brief Deliberate corruptions of the strengthening derivation, for
     * testing only. VeriPB must reject each of them.
     *
     * \ingroup Innards
     */
    namespace cumulative_strengthening_mutation
    {
        /// Emit the honest derivation.
        struct None
        {
        };

        /// Claim a capacity one below the largest load the heights can reach.
        /// The "bound + 1 must fail" check for this rule: it corrupts the
        /// conclusion rather than the route to it.
        struct ClaimOneBetter
        {
        };

        /// Take the divisibility fast path with a divisor that does not divide
        /// every height. Dividing is a sound proof step whatever the divisor,
        /// so this produces a perfectly valid line that simply is not the one
        /// the derived constraint was told it had --- which nothing catches
        /// except the `ia` step pinning each row's content.
        struct BogusDivisor
        {
        };

        /// Raise the tallest task that did *not* qualify for it. The pairwise
        /// conflict test is the only thing standing between the rule and an
        /// unsound constraint, and this is what says so: the derivation itself
        /// runs honestly and every step of it is sound, on a set that is wrong.
        /// Needs a fixture with a task that fails the test, which is what an
        /// R1 control fixture is.
        struct RaiseUnentitled
        {
        };

        /// Take one more than the largest step the division survives, on the
        /// first step of each raise. The step lands on a sound but weaker line,
        /// every later step compounds it, and the row's own `ia` pin is what
        /// rejects. Needs a raise with a step to spare, and throws rather than
        /// passing quietly if given one that has none.
        struct RaiseTooFast
        {
        };
    }

    using CumulativeStrengtheningMutation = std::variant<cumulative_strengthening_mutation::None, cumulative_strengthening_mutation::ClaimOneBetter,
        cumulative_strengthening_mutation::BogusDivisor, cumulative_strengthening_mutation::RaiseUnentitled,
        cumulative_strengthening_mutation::RaiseTooFast>;
}

#endif
