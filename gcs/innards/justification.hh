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
     * \brief The empty hint: a bare RUP carrying no assertion hint. This is what
     * JustifyUsingRUP{} (and hence the Justification variant) holds.
     *
     * \ingroup Innards
     */
    struct NoHint
    {
    };

    /**
     * \brief Specify that an inference can be justified using reverse unit
     * propagation, optionally carrying a typed assertion hint.
     *
     * `JustifyUsingRUP{}` is the bare, nameless RUP (the common case, and the one
     * that lives in the Justification variant). `JustifyUsingRUP{hints::Foo{...}}`
     * is the same RUP inference, but in assertion mode it is asserted under a typed
     * hint (model name + structured fields, e.g. the owning constraint id) built by
     * witness_annotation. The hint never carries explicit proof steps — that is what
     * JustifyByWitness is for — so in normal (Off) proof mode this is byte-identical
     * to a bare RUP regardless of the hint.
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
     * \brief Justify an inference with a *typed witness*, dispatched by proof mode.
     *
     * The pay-for-use, std::function-free explicit-justification interface. The witness
     * is a small struct (in \c gcs::innards::hints, reopened per constraint) that
     * carries everything its justification needs; its consumers are found by ADL on
     * the witness type:
     *
     *   - \c emit_justification(ProofLogger &, const Witness &, const ReasonLiterals &)
     *     — the real eager (and, later, lazy) proof steps (required);
     *   - \c hint_sexpr(const Witness &, NamesAndIDsTracker &) -> SExpr — the
     *     assertion wire form (optional; absent ⇒ coarse-name-only annotation).
     *
     * A \c hint_name member on the witness (static constexpr for a typed witness, a
     * plain member for the generic closure escape) carries the coarse model-level
     * name. \c then_rup picks the ThenRUP (real steps then a RUP for the inference)
     * versus Only (steps stand alone) shape.
     *
     * It holds no std::function: the witness is built by value at the call site
     * (cheap — no type erasure, no heap), and dispatch is compile-time overload
     * resolution. The Simple (proofs-off) tracker never touches the witness, so
     * nothing is emitted or materialised. The only erasure is the future
     * lazy-storage boundary (a per-type emit function pointer).
     *
     * \ingroup Innards
     * \sa Justification
     */
    template <typename Witness_>
    struct JustifyByWitness
    {
        Witness_ witness;
        bool then_rup = true;
    };

    template <typename Witness_>
    JustifyByWitness(Witness_) -> JustifyByWitness<Witness_>;

    template <typename Witness_>
    JustifyByWitness(Witness_, bool) -> JustifyByWitness<Witness_>;

    /**
     * \brief Specify why an inference is justified, for proof logging.
     *
     * The plain (witness-free) justifications. Explicit proof steps are supplied by
     * a typed JustifyByWitness instead, dispatched by overload resolution rather
     * than carried in this variant.
     *
     * \ingroup Innards
     */
    using Justification = std::variant<JustifyUsingRUP<NoHint>, AssertRatherThanJustifying, NoJustificationNeeded>;
}

#endif
