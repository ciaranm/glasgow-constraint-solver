#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_JUSTIFICATION_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_JUSTIFICATION_HH

#include <gcs/innards/proof-fwd.hh>

#ifdef GCS_TRACK_ALL_PROPAGATIONS
#include <source_location>
#endif

#include <functional>
#include <variant>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief Write an explicit justification to the proof, and the specified
     * lines will be deleted after the final RUP statement.
     *
     * \ingroup Innards
     * \sa JustifyExplicitly
     */
    using ExplicitJustificationFunction = std::function<auto(Proof &, std::vector<ProofLine> &)->void>;

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
    using Justification = std::variant<Guess, JustifyUsingRUP, JustifyUsingAssertion, JustifyExplicitly, NoJustificationNeeded>;
}

#endif
