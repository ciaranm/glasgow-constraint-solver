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
     * \brief Write an explicit justification to the proof. Any ProofLevel::Temporary
     * constraints will be wiped after the conclusion is derived. The reason used for
     * the outside inference is provided for convenience.
     *
     * \ingroup Innards
     * \sa JustifyExplicitlyThenRUP
     */
    using ExplicitJustificationFunction = std::function<auto(const ReasonLiterals & reason)->void>;

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
     * \brief Justify an inference from a typed hint witness, dispatched by mode.
     *
     * The single Plan-B recipe: the caller supplies one typed Data witness (via
     * \ref justify_with) and the framework picks the consumer by proof mode. In
     * eager mode \c emit writes the real proof steps, followed by a RUP for the
     * inference itself when \c then_rup (the JustifyExplicitlyThenRUP shape); in
     * assertion mode \c annotation serialises the witness as the assertion's hint
     * and \c emit is not run. An empty \c emit means the inference is pure RUP
     * (no explicit lemma). The witness is captured into the two closures, so this
     * stays a plain (non-template) alternative of \ref Justification.
     *
     * \ingroup Innards
     * \sa Justification
     */
    struct JustifyByData
    {
        std::function<auto(ProofLogger &, const ReasonLiterals &)->void> emit;
        std::function<auto(NamesAndIDsTracker &)->AssertionAnnotation> annotation;
        bool then_rup = true;
    };

    /**
     * \brief Specify why an inference is justified, for proof logging.
     *
     * \ingroup Innards
     */
    using Justification = std::variant<JustifyUsingRUP, JustifyExplicitlyOnly, JustifyExplicitlyThenRUP, AssertRatherThanJustifying, NoJustificationNeeded, JustifyByData>;

    /**
     * \brief Build a JustifyByData from a typed witness.
     *
     * The witness's consumers are found by ADL on its type. \c
     * emit_justification(ProofLogger&, const Data&, const ReasonLiterals&) (the
     * eager/lazy proof steps) is required. \c hint_sexpr(const Data&,
     * NamesAndIDsTracker&) (the assertion wire form) is optional: a witness that
     * provides it is "witness-complete" and its typed fields go into the
     * assertion hint; one that does not still carries the coarse \p hint_name
     * alone. \p hint_name is the coarse, model-level second-field name.
     *
     * \ingroup Innards
     */
    template <typename Data_>
    [[nodiscard]] auto justify_with(Data_ witness, std::string_view hint_name, bool then_rup = true) -> JustifyByData
    {
        JustifyByData result;
        result.emit = [witness](ProofLogger & logger, const ReasonLiterals & reason) { emit_justification(logger, witness, reason); };
        result.then_rup = then_rup;
        if constexpr (requires(NamesAndIDsTracker & names) { hint_sexpr(witness, names); })
            result.annotation = [witness, hint_name](NamesAndIDsTracker & names) { return AssertionAnnotation{.hint_name = hint_name, .hint_fields = hint_sexpr(witness, names)}; };
        else
            result.annotation = [hint_name](NamesAndIDsTracker &) { return AssertionAnnotation{.hint_name = hint_name}; };
        return result;
    }
}

#endif
