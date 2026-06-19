#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_JUSTIFICATION_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_JUSTIFICATION_HH

#include <gcs/innards/assertion_hints.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/names_and_ids_tracker-fwd.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/reason.hh>

#include <functional>
#include <string_view>
#include <utility>
#include <variant>

namespace gcs::innards
{
    /**
     * \brief The explicit proof steps for a justification: writes to the proof,
     * with the inference's reason provided for convenience. Any ProofLevel::Temporary
     * constraints it emits are wiped after the conclusion is derived. Held by
     * JustifyByData::emit.
     *
     * \ingroup Innards
     * \sa JustifyByData
     */
    using ExplicitJustificationFunction = std::function<auto(const ReasonLiterals & reason)->void>;

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
     * \brief Justify an inference with explicit proof steps, dispatched by mode.
     *
     * The single explicit-justification recipe (it replaces JustifyExplicitlyOnly
     * and JustifyExplicitlyThenRUP). In eager mode \c emit writes the real proof
     * steps, followed by a RUP for the inference itself when \c then_rup (the
     * "ThenRUP" shape; \c then_rup == false is the "Only" shape). In assertion
     * mode \c emit is not run: the inference is asserted under its \c annotation
     * if set, otherwise under the annotation passed to infer(). An empty \c emit
     * is a pure-RUP inference.
     *
     * \c annotation is how a constraint attaches a *typed* hint: it builds the
     * AssertionAnnotation from a witness (via that witness's \c hint_sexpr) only
     * in a consuming mode. Constraints that only want the coarse second-field name
     * can leave \c annotation empty and pass it through infer()'s annotation
     * parameter instead.
     *
     * \ingroup Innards
     * \sa Justification
     */
    struct JustifyByData
    {
        ExplicitJustificationFunction emit;
        std::function<auto(NamesAndIDsTracker &)->AssertionAnnotation> annotation;
        bool then_rup = true;
    };

    /**
     * \brief Specify why an inference is justified, for proof logging.
     *
     * \ingroup Innards
     */
    using Justification = std::variant<JustifyUsingRUP, AssertRatherThanJustifying, NoJustificationNeeded, JustifyByData>;
}

#endif
