
#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_REIFIED_DISPATCHER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_REIFIED_DISPATCHER_HH

#include <gcs/innards/justification.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>
#include <gcs/reification.hh>

#include <util/overloaded.hh>

#include <string>
#include <utility>
#include <variant>

namespace gcs::innards
{
    namespace reification_verdict
    {
        /**
         * \brief The constraint can't yet decide whether it must hold or
         * must not hold. The dispatcher will keep the propagator enabled.
         */
        struct StillUndecided
        {
        };

        /**
         * \brief The constraint must hold (the variable bounds prove it).
         * If the reification condition licenses an inference, the
         * dispatcher will infer the appropriate cond literal using the
         * given justification and reason.
         */
        struct MustHold
        {
            Justification justification;
            ReasonFunction reason;
        };

        /**
         * \brief The constraint cannot hold. Same shape as MustHold.
         */
        struct MustNotHold
        {
            Justification justification;
            ReasonFunction reason;
        };
    }

    /**
     * \brief Result of a constraint's `infer_cond_when_undecided` pass:
     * either the constraint is still undecided, or it must hold / must not
     * hold (in which case the constraint provides the materials needed for
     * the cond inference, and the dispatcher decides whether and which
     * literal to infer).
     */
    using ReificationVerdict = std::variant<
        reification_verdict::StillUndecided,
        reification_verdict::MustHold,
        reification_verdict::MustNotHold>;

    /**
     * \brief Install a single propagator that dispatches on the current state
     * of a reification condition, calling one of three user-supplied passes.
     *
     * Almost every reified constraint follows the same skeleton: when the
     * constraint must hold (cond is true), enforce it; when it must not hold
     * (cond is false), enforce the negation; while cond is still undecided,
     * watch the variable state and detect whether the constraint's verdict
     * is now forced. This helper takes three callables and wires up the
     * dispatch and triggers.
     *
     * `enforce_constraint_must_hold(state, inference, logger, cond_lit)` and
     * `enforce_constraint_must_not_hold(state, inference, logger, cond_lit)`
     * each return a PropagatorState; they receive the cond literal (a
     * Literal) for use in their reasons.
     *
     * `infer_cond_when_undecided(state, inference, logger, cond_lit)`
     * returns a ReificationVerdict variant. The cond_lit is the
     * reification's condition (so the constraint can use it when building
     * its scaffolding's reason); the constraint must not consult the
     * reification's policy flags. If the verdict is StillUndecided, the
     * dispatcher returns Enable; if it is MustHold or MustNotHold, the
     * dispatcher consults the reification kind to decide whether to infer
     * cond=TRUE or cond=FALSE (or do nothing), uses the justification and
     * reason carried by the verdict, and returns DisableUntilBacktrack.
     *
     * The caller supplies the constraint-side triggers. When the
     * reification condition is initially Undecided, this helper appends
     * `cond.var` to `triggers.on_change`. If the initial reification state
     * is Deactivated, no propagator is installed at all.
     */
    template <typename EnforceMustHold_, typename EnforceMustNotHold_, typename InferCondWhenUndecided_>
    auto install_reified_dispatcher(
        Propagators & propagators,
        const State & initial_state,
        const ReificationCondition & reif_cond,
        Triggers triggers,
        EnforceMustHold_ enforce_constraint_must_hold,
        EnforceMustNotHold_ enforce_constraint_must_not_hold,
        InferCondWhenUndecided_ infer_cond_when_undecided,
        const std::string & name) -> void
    {
        auto initial = initial_state.test_reification_condition(reif_cond);
        if (std::holds_alternative<evaluated_reif::Deactivated>(initial))
            return;
        if (std::holds_alternative<evaluated_reif::Undecided>(initial)) {
            const auto & undecided = std::get<evaluated_reif::Undecided>(initial);
            triggers.on_change.push_back(undecided.cond.var);
        }

        propagators.install(
            [reif_cond,
                enforce_constraint_must_hold = std::move(enforce_constraint_must_hold),
                enforce_constraint_must_not_hold = std::move(enforce_constraint_must_not_hold),
                infer_cond_when_undecided = std::move(infer_cond_when_undecided)](
                const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                return overloaded{
                    [&](const evaluated_reif::MustHold & reif) {
                        return enforce_constraint_must_hold(state, inference, logger, reif.cond);
                    },
                    [&](const evaluated_reif::MustNotHold & reif) {
                        return enforce_constraint_must_not_hold(state, inference, logger, reif.cond);
                    },
                    [&](const evaluated_reif::Undecided & reif) {
                        return overloaded{
                            [&](const reification_verdict::StillUndecided &) {
                                return PropagatorState::Enable;
                            },
                            [&](const reification_verdict::MustHold & h) {
                                if (reif.set_cond_if_must_hold)
                                    inference.infer(logger, reif.cond, h.justification, h.reason);
                                else if (reif.set_not_cond_if_must_hold)
                                    inference.infer(logger, ! reif.cond, h.justification, h.reason);
                                return PropagatorState::DisableUntilBacktrack;
                            },
                            [&](const reification_verdict::MustNotHold & n) {
                                if (reif.set_not_cond_if_must_not_hold)
                                    inference.infer(logger, ! reif.cond, n.justification, n.reason);
                                return PropagatorState::DisableUntilBacktrack;
                            }}
                            .visit(infer_cond_when_undecided(state, inference, logger, reif.cond));
                    },
                    [&](const evaluated_reif::Deactivated &) {
                        return PropagatorState::DisableUntilBacktrack;
                    }}
                    .visit(state.test_reification_condition(reif_cond));
            },
            triggers, name);
    }
}

#endif
