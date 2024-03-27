#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_JUSTIFICATION_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_JUSTIFICATION_HH

#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/reason.hh>

#ifdef GCS_TRACK_ALL_PROPAGATIONS
#include <source_location>
#endif

#include <functional>
#include <variant>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief Write an explicit justification to the proof. Any ProofLevel::Temporary
     * constraints will be wiped after the conclusion is derived.
     *
     * \ingroup Innards
     * \sa JustifyExplicitly
     */
    using ExplicitJustificationFunction = std::function<auto()->void>;

    /**
     * \brief Justification for something that is actually a guess, not an
     * inferred decision.
     *
     * \ingroup Innards
     * \sa Justification
     */
    struct Guess
    {
    };

    /**
     * \brief Specify that an inference requires an explicit justification in
     * the proof log.
     *
     * \ingroup Innards
     * \sa Justification
     */
    struct JustifyExplicitly
    {
        ExplicitJustificationFunction add_proof_steps;
        Reason reason;
#ifdef GCS_TRACK_ALL_PROPAGATIONS
        std::source_location where;
#endif

        explicit JustifyExplicitly(const ExplicitJustificationFunction & a,
            Reason r
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            const std::source_location & w = std::source_location::current()
#endif
                ) :
            add_proof_steps(a),
            reason(std::move(r))
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            where(w)
#endif
        {
        }
    };

    /**
     * \brief Specify that an inference can be justified using reverse unit
     * propagation.
     *
     * \ingroup Innards
     * \sa Justification
     */
    struct JustifyUsingRUP
    {
        Reason reason;
#ifdef GCS_TRACK_ALL_PROPAGATIONS
        std::source_location where;
#endif

#ifdef GCS_TRACK_ALL_PROPAGATIONS
        explicit JustifyUsingRUP(Reason r, const std::source_location & w = std::source_location::current()) :
            reason(std::move(r)),
            where(w)
        {
        }
#else
        explicit JustifyUsingRUP(Reason r) :
            reason(std::move(r))
        {
        }
#endif
    };

    /**
     * \brief Specify that an inference will be asserted rather than justified.
     *
     * \ingroup Innards
     * \sa Justification
     */
    struct AssertRatherThanJustifying
    {
        Reason reason;
#ifdef GCS_TRACK_ALL_PROPAGATIONS
        std::source_location where;
#endif

#ifdef GCS_TRACK_ALL_PROPAGATIONS
        explicit AssertRatherThanJustifying(Reason r, const std::source_location & w = std::source_location::current()) :
            reason(std::move(r)),
            where(w)
        {
        }
#else
        explicit AssertRatherThanJustifying(Reason r) :
            reason(std::move(r))
        {
        }
#endif
    };

    /**
     * \brief Specify that an inference does not require justification.
     *
     * \ingroup Innards
     * \sa Justification
     */
    struct NoJustificationNeeded
    {
    };

    /**
     * \brief Specify why an inference is justified, for proof logging.
     *
     * \ingroup Innards
     */
    using Justification = std::variant<Guess, JustifyUsingRUP, JustifyExplicitly, AssertRatherThanJustifying, NoJustificationNeeded>;
}

#endif
