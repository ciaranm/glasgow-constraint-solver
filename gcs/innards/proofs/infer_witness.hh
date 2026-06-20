#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_INFER_WITNESS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_INFER_WITNESS_HH

#include <gcs/expression.hh>
#include <gcs/innards/assertion_hints.hh>
#include <gcs/innards/justification.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/pseudo_boolean.hh>
#include <gcs/innards/proofs/simplify_literal.hh>
#include <gcs/innards/reason.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <optional>
#include <string_view>

#include <util/overloaded.hh>

namespace gcs::innards
{
    /**
     * \brief A witness has explicit proof steps if it provides an emit_justification
     * overload (found by ADL). Witnesses that do not are the pure-RUP capability
     * tier: their inference is RUP-derivable on its own, so eager mode emits just
     * the RUP (byte-identical to JustifyUsingRUP) and they carry only an assertion
     * hint. Used to pick the eager strategy without a runtime flag.
     *
     * \ingroup Innards
     */
    template <typename Witness_>
    concept WitnessHasExplicitSteps = requires(ProofLogger & logger, const Witness_ & witness, const ReasonLiterals & reason) {
        emit_justification(logger, witness, reason);
    };

    /**
     * \brief Build the assertion annotation for a typed witness.
     *
     * If the witness has a \c hint_sexpr overload (found by ADL) it is a structured
     * hint: emit the coarse \c hint_name plus the serialised fields. Otherwise, if
     * the witness carries a non-empty coarse \c hint_name, emit just that; if it is
     * empty, fall back to the annotation passed to infer() (so the generic closure
     * escape with no coarse name behaves exactly like the old un-annotated
     * JustifyByData).
     *
     * \ingroup Innards
     */
    template <typename Witness_>
    [[nodiscard]] auto witness_annotation(ProofLogger & logger, const Witness_ & witness,
        const std::optional<AssertionAnnotation> & fallback) -> std::optional<AssertionAnnotation>
    {
        if constexpr (requires { hint_sexpr(witness, logger.names_and_ids_tracker()); }) {
            return AssertionAnnotation{.hint_name = witness.hint_name,
                .hint_fields = hint_sexpr(witness, logger.names_and_ids_tracker())};
        }
        else {
            if (! std::string_view{witness.hint_name}.empty())
                return AssertionAnnotation{.hint_name = witness.hint_name};
            else
                return fallback;
        }
    }

    /**
     * \brief The mode-dispatched back end for a JustifyByWitness inference.
     *
     * Mirrors the JustifyByData arm of ProofLogger::infer, but resolves the
     * justification by compile-time overload resolution on the witness type rather
     * than through a std::function:
     *
     *   - above AssertionLevel::Inferences: nothing (the inference is not asserted);
     *   - assertion mode: assert the inference under its reason, annotated by
     *     witness_annotation (a typed hint if the witness has \c hint_sexpr);
     *   - eager mode: run \c emit_justification (the real proof steps) at a
     *     temporary level, then RUP the inference under the reason when \c then_rup.
     *
     * A NotInRange conclusion that cannot become a single range literal falls back
     * to one per-value inference, exactly as ProofLogger::infer does.
     *
     * Only ever reached with a non-null logger (the Simple tracker never builds or
     * consumes the witness), so this is pure proof-on work.
     *
     * \ingroup Innards
     */
    template <typename Witness_>
    auto infer_witness(ProofLogger & logger, const Literal & lit, const Witness_ & witness, bool then_rup,
        const ReasonLiterals & reason, const std::optional<AssertionAnnotation> & fallback_annotation = std::nullopt) -> void
    {
        if (const auto * cond = std::get_if<IntegerVariableCondition>(&lit))
            if (cond->op == VariableConditionOperator::NotInRange) {
                auto needs_per_value_fallback = overloaded{
                    [&](const SimpleIntegerVariableID & v) { return ! logger.names_and_ids_tracker().has_bit_representation(v); },
                    [&](const ViewOfIntegerVariableID &) { return true; },
                    [&](const ConstantIntegerVariableID &) { return false; }}
                                                    .visit(cond->var);
                if (needs_per_value_fallback) {
                    for (Integer val = cond->value; val <= cond->upper_value; ++val)
                        infer_witness(logger, cond->var != val, witness, then_rup, reason, fallback_annotation);
                    return;
                }
            }

        if (logger.get_assertion_level() > AssertionLevel::Inferences)
            return;

        if (logger.get_assertion_level() != AssertionLevel::Off) {
            if (! is_literally_true(lit)) {
                auto annotation = witness_annotation(logger, witness, fallback_annotation);
                logger.emit_under_reason(AssertProofRule{}, WPBSum{} + 1_i * lit >= 1_i, ProofLevel::Current, reason, annotation);
            }
            return;
        }

        if constexpr (WitnessHasExplicitSteps<Witness_>) {
            if (then_rup) {
                overloaded{
                    [&](const TrueLiteral &) {},
                    [&](const FalseLiteral &) {},
                    [&]<typename T_>(const VariableConditionFrom<T_> & cond) { logger.names_and_ids_tracker().need_proof_name(cond); }}
                    .visit(simplify_literal(logger.names_and_ids_tracker(), lit));
            }
            auto t = logger.temporary_proof_level();
            emit_justification(logger, witness, reason);
            if (then_rup)
                logger.infer(lit, JustifyUsingRUP{}, reason);
            logger.forget_proof_level(t);
        }
        else {
            // Pure-RUP witness: no explicit steps, byte-identical to JustifyUsingRUP.
            if (! is_literally_true(lit))
                logger.emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * lit >= 1_i, ProofLevel::Current);
        }
    }

    namespace hints
    {
        /**
         * \brief The tier-3 closure escape: keep an inline emit closure but carry it
         * through the typed witness path.
         *
         * For a justification with no liftable typed witness (the long tail of
         * one-off explicit steps), this wraps the existing inline \c emit closure so
         * it flows through JustifyByWitness. It is pay-for-use the same way a typed
         * witness is — built by value, the closure captures by reference, no
         * std::function and no heap — and it degrades gracefully: in assertion mode
         * it has no \c hint_sexpr, so it carries only the coarse \c hint_name (empty
         * by default, i.e. fall back to infer()'s annotation).
         *
         * \ingroup Innards
         */
        template <typename Emit_>
        struct InlineEmit
        {
            Emit_ emit;
            std::string_view hint_name = "";
        };

        template <typename Emit_>
        auto emit_justification(ProofLogger &, const InlineEmit<Emit_> & witness, const ReasonLiterals & reason) -> void
        {
            witness.emit(reason);
        }

        /**
         * \brief The pure-RUP escape: an inference that is RUP-derivable on its own
         * but wants a coarse model-level name in assertion mode.
         *
         * This is the witness form of "JustifyUsingRUP plus a coarse hint name".
         * It has no emit_justification (so eager mode emits just the RUP,
         * byte-identical to JustifyUsingRUP) and no hint_sexpr (so the annotation is
         * the coarse name alone). The home for a constraint's coarse name until it
         * grows a typed, structured witness.
         *
         * \ingroup Innards
         */
        struct CoarseHint
        {
            std::string_view hint_name;
        };
    }
}

#endif
