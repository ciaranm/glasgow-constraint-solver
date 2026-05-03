
#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_REIFIED_DISPATCHER_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_REIFIED_DISPATCHER_HH

#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>
#include <gcs/reification.hh>

#include <util/overloaded.hh>

#include <string>
#include <utility>
#include <variant>

namespace gcs::innards
{
    /**
     * \brief Install a single propagator that dispatches on the current state
     * of a reification condition, calling one of three user-supplied passes.
     *
     * Almost every reified constraint follows the same skeleton: when the
     * constraint must hold (cond is true), enforce it; when it must not hold
     * (cond is false), enforce the negation; while cond is still undecided,
     * watch the variable state and infer cond when it becomes forced. This
     * helper takes three callables and wires up the dispatch and triggers.
     *
     * The callables are invoked with `(const State &, auto & inference,
     * ProofLogger *, ...)` and must return PropagatorState.
     * `enforce_constraint_must_hold` and `enforce_constraint_must_not_hold`
     * receive the cond literal (a Literal) for use in their reasons;
     * `infer_cond_when_undecided` receives the evaluated_reif::Undecided
     * struct so it can consult its `set_cond_if_must_hold` etc. flags.
     *
     * The caller supplies the constraint-side triggers (on_bounds,
     * on_change, on_instantiated). When `initial_evaluated` is Undecided,
     * this helper appends `cond.var` to `triggers.on_change` so the
     * dispatcher wakes up when cond changes.
     *
     * `initial_evaluated` is the result of evaluating the reification
     * condition against the initial state; the caller computes it once
     * (typically in `prepare()`) and passes it in. This keeps the helper
     * usable from `install_propagators()`, which has no `initial_state`.
     *
     * If `initial_evaluated` is Deactivated, no propagator is installed.
     */
    template <typename EnforceMustHold_, typename EnforceMustNotHold_, typename InferCondWhenUndecided_>
    auto install_reified_dispatcher(
        Propagators & propagators,
        const EvaluatedReificationCondition & initial_evaluated,
        const ReificationCondition & reif_cond,
        Triggers triggers,
        EnforceMustHold_ enforce_constraint_must_hold,
        EnforceMustNotHold_ enforce_constraint_must_not_hold,
        InferCondWhenUndecided_ infer_cond_when_undecided,
        const std::string & name) -> void
    {
        if (std::holds_alternative<evaluated_reif::Deactivated>(initial_evaluated))
            return;
        if (std::holds_alternative<evaluated_reif::Undecided>(initial_evaluated)) {
            const auto & undecided = std::get<evaluated_reif::Undecided>(initial_evaluated);
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
                        return infer_cond_when_undecided(state, inference, logger, reif);
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
