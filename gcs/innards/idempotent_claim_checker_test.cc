#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <catch2/catch_test_macros.hpp>

#include <cstdlib>

using namespace gcs;
using namespace gcs::innards;

// The GCS_CHECK_IDEMPOTENT_CLAIMS re-run checker. This is a separate binary
// from propagators_test because the flag is read once per process, and the
// checker's re-runs would distort that file's run-count assertions. Every test
// case sets the variable before its first propagate() call, so the once-only
// read sees it whichever case runs first.

namespace
{
    auto enable_checker() -> void
    {
        setenv("GCS_CHECK_IDEMPOTENT_CLAIMS", "1", 1);
    }
}

TEST_CASE("A lying idempotence claim is caught by the checker")
{
    enable_checker();

    State state;
    Propagators propagators;
    auto x = state.allocate_integer_variable_with_state(0_i, 10_i);

    // Shaves one value off x per run, so an immediate re-run always infers
    // more: the claim is a lie, and the checker must abort the solve.
    Triggers triggers;
    triggers.on_change = {x};
    propagators.install(
        ConstraintID{NumberedConstraint{1}},
        [x](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            if (state.upper_bound(x) > 0_i)
                inference.infer(logger, x < state.upper_bound(x), NoJustificationNeeded{}, NoReason{});
            return PropagatorState::EnableButIdempotent;
        },
        triggers);

    CHECK_THROWS_AS(propagators.propagate(Literals{}, state, nullptr), UnexpectedException);
}

TEST_CASE("An honest idempotence claim passes the checker")
{
    enable_checker();

    State state;
    Propagators propagators;
    auto x = state.allocate_integer_variable_with_state(0_i, 10_i);

    int runs = 0;
    Triggers triggers;
    triggers.on_change = {x};
    propagators.install(
        ConstraintID{NumberedConstraint{1}},
        [&runs, x](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            ++runs;
            if (state.upper_bound(x) > 5_i)
                inference.infer(logger, x < 6_i, NoJustificationNeeded{}, NoReason{});
            return PropagatorState::EnableButIdempotent;
        },
        triggers);

    REQUIRE(propagators.propagate(Literals{}, state, nullptr));
    CHECK(state.upper_bound(x) == 5_i);
    // Once for the claiming run, once for the checker's re-run; the claim then
    // suppresses the self-requeue, so there is no third run.
    CHECK(runs == 2);
}

TEST_CASE("A downgraded claim is neither honoured nor checked")
{
    enable_checker();

    State state;
    Propagators propagators;
    auto x = state.allocate_integer_variable_with_state(0_i, 3_i);

    // The same liar as above, but with an aliased trigger scope: install()
    // ignores its claims, so the checker must not fire, and ordinary
    // self-requeue walks x down one value per round to the fixpoint.
    int runs = 0;
    Triggers triggers;
    triggers.on_change = {x, x};
    propagators.install(
        ConstraintID{NumberedConstraint{1}},
        [&runs, x](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            ++runs;
            if (state.upper_bound(x) > 0_i)
                inference.infer(logger, x < state.upper_bound(x), NoJustificationNeeded{}, NoReason{});
            return PropagatorState::EnableButIdempotent;
        },
        triggers);

    REQUIRE(propagators.propagate(Literals{}, state, nullptr));
    CHECK(state.upper_bound(x) == 0_i);
    CHECK(runs == 4);
}
