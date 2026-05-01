#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_JUSTIFICATION_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_JUSTIFICATION_HH

#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/reason.hh>

#include <functional>
#include <variant>

namespace gcs::innards
{
    /**
     * \brief Write an explicit justification to the proof. Any ProofLevel::Temporary
     * constraints will be wiped after the conclusion is derived. The reason used for
     * the outside inference is provided for convenience.
     *
     * \ingroup Innards
     * \sa JustifyExplicitlyThenRUP
     */
    using ExplicitJustificationFunction = std::function<auto(const ReasonFunction & reason)->void>;

    /**
     * \brief Specify that an inference requires an explicit justification in
     * the proof log. There will be no RUP step at the end of the explicit justifiction.
     *
     * \ingroup Innards
     * \sa Justification
     */
    struct JustifyExplicitlyOnly
    {
        ExplicitJustificationFunction add_proof_steps;

        explicit JustifyExplicitlyOnly(const ExplicitJustificationFunction & a) :
            add_proof_steps(a)
        {
        }
    };

    /**
     * \brief Specify that an inference requires an explicit justification in
     * the proof log. This will be followed by a final RUP step for the inference itself.
     *
     * \ingroup Innards
     * \sa Justification
     */
    struct JustifyExplicitlyThenRUP
    {
        ExplicitJustificationFunction add_proof_steps;

        explicit JustifyExplicitlyThenRUP(const ExplicitJustificationFunction & a) :
            add_proof_steps(a)
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
        explicit JustifyUsingRUP()
        {
        }
    };

    /**
     * \brief Specify that an inference will be asserted rather than justified.
     *
     * \ingroup Innards
     * \sa Justification
     */
    struct AssertRatherThanJustifying
    {
        explicit AssertRatherThanJustifying()
        {
        }
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
    using Justification = std::variant<JustifyUsingRUP, JustifyExplicitlyOnly, JustifyExplicitlyThenRUP, AssertRatherThanJustifying, NoJustificationNeeded>;
}

#endif
