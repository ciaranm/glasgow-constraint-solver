#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_JUSTIFICATION_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_JUSTIFICATION_HH

#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/hints.hh>
#include <gcs/innards/proofs/names_and_ids_tracker-fwd.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/reason.hh>

#include <utility>
#include <variant>

namespace gcs::innards
{
    /**
     * \brief Whether a JustifyExplicitly appends a RUP derivation of the inferred
     * literal after its explicit proof steps, or lets the steps stand alone.
     *
     * This was historically a bare `bool then_rup`; it is spelled as an enum, and is
     * a mandatory argument at every JustifyExplicitly call site, so the proof shape
     * is always legible rather than hidden behind an unlabelled true/false.
     *
     * \ingroup Innards
     * \sa JustifyExplicitly
     */
    enum class ThenRUP
    {
        Yes, ///< emit the explicit steps, then RUP the inferred literal under the reason
        No   ///< the explicit steps stand alone (they conclude the inference themselves)
    };

    /**
     * \brief Specify that an inference can be justified using reverse unit
     * propagation, optionally carrying a typed assertion hint.
     *
     * `JustifyUsingRUP{}` is the bare, nameless RUP (the common case, and the one
     * that lives in the Justification variant). `JustifyUsingRUP{hints::Foo{...}}`
     * is the same RUP inference, but in assertion mode it is asserted under a typed
     * hint (model name plus optional structured fields, e.g. the owning constraint
     * id) built by hint_annotation. The hint never carries explicit proof steps —
     * that is what JustifyExplicitly is for — so in normal (Off) proof mode this is
     * byte-identical to a bare RUP regardless of the hint.
     *
     * \ingroup Innards
     * \sa Justification
     */
    template <typename Hint_ = NoHint>
    struct JustifyUsingRUP
    {
        [[no_unique_address]] Hint_ hint{};
    };

    JustifyUsingRUP() -> JustifyUsingRUP<NoHint>;

    template <typename Hint_>
    JustifyUsingRUP(Hint_) -> JustifyUsingRUP<Hint_>;

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
     * \brief Justify an inference with *explicit proof steps*, dispatched by proof
     * mode, optionally carrying a typed assertion hint.
     *
     * The pay-for-use, std::function-free explicit-justification interface, mirroring
     * JustifyUsingRUP: both are parameterised on an optional \c Hint_, and the hint
     * means the same thing in both (a typed assertion annotation, orthogonal to how
     * the inference is proved). The difference is the \c emit:
     *
     *   - \c emit is a callable `(const ReasonLiterals &) -> void` that writes the
     *     real proof steps. It is built by value at the call site (a lambda, or a
     *     storable struct with operator() for replay at backtrack time) — no type
     *     erasure, no heap, no std::function. The Simple (proofs-off) tracker never
     *     touches it, so nothing is emitted or materialised when proofs are off.
     *   - \c then_rup picks the proof shape: ThenRUP::Yes emits the steps at a
     *     temporary level then RUPs the inferred literal under the reason; ThenRUP::No
     *     lets the steps conclude the inference themselves.
     *   - \c hint is the assertion-mode annotation (NoHint by default), resolved by
     *     hint_annotation exactly as for JustifyUsingRUP. In Off mode it is ignored,
     *     so the hint never changes the emitted proof.
     *
     * The only erasure is the future lazy-storage boundary (a per-type emit function
     * pointer).
     *
     * \ingroup Innards
     * \sa Justification
     */
    template <typename Emit_, typename Hint_ = NoHint>
    struct JustifyExplicitly
    {
        Emit_ emit;
        ThenRUP then_rup;
        [[no_unique_address]] Hint_ hint{};
    };

    template <typename Emit_>
    JustifyExplicitly(Emit_, ThenRUP) -> JustifyExplicitly<Emit_, NoHint>;

    template <typename Emit_, typename Hint_>
    JustifyExplicitly(Emit_, ThenRUP, Hint_) -> JustifyExplicitly<Emit_, Hint_>;

    /**
     * \brief Specify why an inference is justified, for proof logging.
     *
     * The plain (emit-free) justifications. Explicit proof steps are supplied by a
     * JustifyExplicitly instead, dispatched by overload resolution rather than
     * carried in this variant.
     *
     * \ingroup Innards
     */
    using Justification = std::variant<JustifyUsingRUP<NoHint>, AssertRatherThanJustifying, NoJustificationNeeded>;
}

#endif
