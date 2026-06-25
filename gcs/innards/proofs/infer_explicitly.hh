#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_INFER_EXPLICITLY_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_INFER_EXPLICITLY_HH

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
     * \brief Build the assertion annotation for a typed hint.
     *
     * Shared by JustifyUsingRUP and JustifyExplicitly: the hint axis is the same for
     * both. Three tiers, resolved at compile time on the hint type:
     *
     *   - if the hint has a \c hint_sexpr overload (found by ADL) it is a structured
     *     hint: emit the coarse \c hint_name plus the serialised fields;
     *   - else if it carries a (non-empty) \c hint_name member it is a coarse hint:
     *     emit just that name;
     *   - else (NoHint, an empty name, or a bare emit closure) fall back to the
     *     supplied annotation.
     *
     * \ingroup Innards
     */
    template <typename Hint_>
    [[nodiscard]] auto hint_annotation(ProofLogger & logger, const Hint_ & hint,
        const std::optional<AssertionAnnotation> & fallback) -> std::optional<AssertionAnnotation>
    {
        if constexpr (requires { hint_sexpr(hint, logger.names_and_ids_tracker()); }) {
            return AssertionAnnotation{.hint_name = hint.hint_name,
                .hint_fields = hint_sexpr(hint, logger.names_and_ids_tracker())};
        }
        else if constexpr (requires { std::string_view{hint.hint_name}; }) {
            if (! std::string_view{hint.hint_name}.empty())
                return AssertionAnnotation{.hint_name = hint.hint_name};
            else
                return fallback;
        }
        else {
            return fallback;
        }
    }

    /**
     * \brief Emit a JustifyExplicitly's explicit proof steps.
     *
     * The \c emit is either a `(const ReasonLiterals &) -> void` callable (an inline
     * lambda, the common case) or a named struct providing an \c emit_justification
     * overload by ADL (a fat witness stored in a reification verdict, where the
     * logger is necessarily deferred to emit time because a lambda type cannot be
     * named in the verdict's return type). Dispatch is compile time.
     *
     * \ingroup Innards
     */
    template <typename Emit_>
    auto emit_explicit_steps(ProofLogger & logger, const Emit_ & emit, const ReasonLiterals & reason) -> void
    {
        if constexpr (requires { emit(reason); })
            emit(reason);
        else
            emit_justification(logger, emit, reason);
    }

    /**
     * \brief The mode-dispatched back end for a JustifyExplicitly inference.
     *
     * The explicit-steps counterpart to ProofLogger::infer's plain arms, taking the
     * emit and the assertion hint as separate arguments (rather than a std::function
     * or a single bundled justification struct):
     *
     *   - above AssertionLevel::Inferences: nothing (the inference is not asserted);
     *   - assertion mode: assert the inference under its reason, annotated by
     *     the resolved hint (explicit hint, else emit's own, else the fallback);
     *   - eager mode: run the explicit steps at a temporary level, then RUP the
     *     inference under the reason when \c then_rup is ThenRUP::Yes.
     *
     * A NotInRange conclusion that cannot become a single range literal falls back
     * to one per-value inference, exactly as ProofLogger::infer does.
     *
     * Only ever reached with a non-null logger (the Simple tracker never builds or
     * consumes the emit/hint), so this is pure proof-on work.
     *
     * \ingroup Innards
     */
    template <typename Emit_, typename Hint_>
    auto infer_explicitly(ProofLogger & logger, const Literal & lit, const Emit_ & emit, ThenRUP then_rup,
        const ReasonLiterals & reason, const Hint_ & hint,
        const std::optional<AssertionAnnotation> & fallback_annotation = std::nullopt) -> void
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
                        infer_explicitly(logger, cond->var != val, emit, then_rup, reason, hint, fallback_annotation);
                    return;
                }
            }

        if (logger.get_assertion_level() > AssertionLevel::Inferences)
            return;

        if (logger.get_assertion_level() != AssertionLevel::Off) {
            if (! is_literally_true(lit)) {
                // Annotation precedence: the explicit hint wins if it advertises
                // anything; else the emit's own advertisement (a named fat witness
                // carrying its own hint_sexpr / hint_name); else the call site's
                // fallback. A bare emit closure advertises nothing, so it resolves
                // straight to the fallback.
                auto annotation = hint_annotation(logger, hint, hint_annotation(logger, emit, fallback_annotation));
                logger.emit_under_reason(AssertProofRule{}, WPBSum{} + 1_i * lit >= 1_i, ProofLevel::Current, reason, annotation);
            }
            return;
        }

        if (then_rup == ThenRUP::Yes) {
            overloaded{
                [&](const TrueLiteral &) {},
                [&](const FalseLiteral &) {},
                [&]<typename T_>(const VariableConditionFrom<T_> & cond) { logger.names_and_ids_tracker().need_proof_name(cond); }}
                .visit(simplify_literal(logger.names_and_ids_tracker(), lit));
        }
        auto t = logger.temporary_proof_level();
        emit_explicit_steps(logger, emit, reason);
        if (then_rup == ThenRUP::Yes)
            logger.infer(lit, JustifyUsingRUP{}, reason);
        logger.forget_proof_level(t);
    }
}

#endif
