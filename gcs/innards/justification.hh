#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_JUSTIFICATION_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_JUSTIFICATION_HH

#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>

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

    using Reason = Literals;

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
    struct JustifyExplicitlyBecauseOf
    {
        ExplicitJustificationFunction add_proof_steps;
        Reason reason;
#ifdef GCS_TRACK_ALL_PROPAGATIONS
        std::source_location where;

        explicit JustifyExplicitlyBecauseOf(const ExplicitJustificationFunction & a,
            Reason r,
            const std::source_location & w = std::source_location::current()) :
            add_proof_steps(a),
            reason(std::move(r)),
            where(w)
        {
        }
#else
#endif
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
#ifdef GCS_TRACK_ALL_PROPAGATIONS
        std::source_location where;

        explicit JustifyExplicitly(const ExplicitJustificationFunction & a,
                const std::source_location & w = std::source_location::current()) :
            add_proof_steps(a),
            where(w)
        {
        }
#else
#endif
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
#ifdef GCS_TRACK_ALL_PROPAGATIONS
        std::source_location where;

        explicit JustifyUsingRUP(const std::source_location & w = std::source_location::current()) :
            where(w)
        {
        }
#else
#endif
    };

    /**
     * \brief Specify that an inference can be justified using reverse unit
     * propagation.
     *
     * \ingroup Innards
     * \sa Justification
     */
    struct JustifyUsingRUPBecauseOf
    {
        Reason reason;
#ifdef GCS_TRACK_ALL_PROPAGATIONS
        std::source_location where;
#endif

#ifdef GCS_TRACK_ALL_PROPAGATIONS
        explicit JustifyUsingRUPBecauseOf(Reason r, const std::source_location & w = std::source_location::current()) :
            reason(std::move(r)),
            where(w)
        {
        }
#else
        explicit JustifyUsingRUPBecauseOf(Reason r) :
            reason(std::move(r))
        {
        }
#endif
    };

    /**
     * \brief Specify that an inference needs to be asserted rather than
     * justified.
     *
     * \ingroup Innards
     * \sa Justification
     */
    struct JustifyUsingAssertion
    {
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
    using Justification = std::variant<Guess, JustifyUsingRUP, JustifyUsingRUPBecauseOf, JustifyUsingAssertion, JustifyExplicitly, JustifyExplicitlyBecauseOf, NoJustificationNeeded>;
}

#endif
