#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <catch2/catch_test_macros.hpp>

using namespace gcs;
using namespace gcs::innards;

// Wake semantics for PropagatorState::EnableButIdempotent: a claiming run's own
// inferences must not re-wake it, everything else about waking is unchanged, and
// install() must ignore claims from propagators whose trigger scope aliases a
// variable. The claim checker (GCS_CHECK_IDEMPOTENT_CLAIMS) is deliberately not
// enabled here -- its re-runs would distort the run counts -- and lives in
// idempotent_claim_checker_test.cc instead.

namespace
{
    // A propagator that caps x at 5 in one go, honestly idempotent: a re-run
    // against the domains it left behind infers nothing.
    auto install_capping_propagator(
        Propagators & propagators, SimpleIntegerVariableID x, const Triggers & triggers, PropagatorState state_to_return, int & runs) -> void
    {
        propagators.install(
            ConstraintID{NumberedConstraint{1}},
            [&runs, x, state_to_return](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                ++runs;
                if (state.upper_bound(x) > 5_i)
                    inference.infer(logger, x < 6_i, NoJustificationNeeded{}, NoReason{});
                return state_to_return;
            },
            triggers);
    }
}

TEST_CASE("Claiming propagator is not re-woken by its own inference")
{
    State state;
    Propagators propagators;
    auto x = state.allocate_integer_variable_with_state(0_i, 10_i);

    int runs = 0;
    Triggers triggers;
    triggers.on_change = {x};
    install_capping_propagator(propagators, x, triggers, PropagatorState::EnableButIdempotent, runs);

    REQUIRE(propagators.propagate(Literals{}, state, nullptr));
    CHECK(state.upper_bound(x) == 5_i);
    CHECK(runs == 1);
}

TEST_CASE("Without a claim, a propagator is re-woken by its own inference")
{
    State state;
    Propagators propagators;
    auto x = state.allocate_integer_variable_with_state(0_i, 10_i);

    int runs = 0;
    Triggers triggers;
    triggers.on_change = {x};
    install_capping_propagator(propagators, x, triggers, PropagatorState::Enable, runs);

    REQUIRE(propagators.propagate(Literals{}, state, nullptr));
    CHECK(state.upper_bound(x) == 5_i);
    CHECK(runs == 2);
}

TEST_CASE("A claimant's inference wakes a sharing propagator, whose inference re-wakes the claimant")
{
    State state;
    Propagators propagators;
    auto x = state.allocate_integer_variable_with_state(0_i, 10_i);
    auto y = state.allocate_integer_variable_with_state(0_i, 10_i);

    // The claimant's scope is {x, y}: first cap x at 5, and once y is capped at
    // 7 (by the second propagator, below) cap x at 2. Both runs are honestly
    // idempotent: each leaves its own guard false.
    int claimant_runs = 0;
    Triggers claimant_triggers;
    claimant_triggers.on_change = {x, y};
    propagators.install(
        ConstraintID{NumberedConstraint{1}},
        [&claimant_runs, x, y](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            ++claimant_runs;
            if (state.upper_bound(x) > 5_i)
                inference.infer(logger, x < 6_i, NoJustificationNeeded{}, NoReason{});
            else if (state.upper_bound(y) <= 7_i && state.upper_bound(x) > 2_i)
                inference.infer(logger, x < 3_i, NoJustificationNeeded{}, NoReason{});
            return PropagatorState::EnableButIdempotent;
        },
        claimant_triggers);

    // The follower watches x and caps y at 7 once x is capped at 5.
    int follower_runs = 0;
    Triggers follower_triggers;
    follower_triggers.on_change = {x};
    propagators.install(
        ConstraintID{NumberedConstraint{2}},
        [&follower_runs, x, y](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            ++follower_runs;
            if (state.upper_bound(x) <= 5_i && state.upper_bound(y) > 7_i)
                inference.infer(logger, y < 8_i, NoJustificationNeeded{}, NoReason{});
            return PropagatorState::Enable;
        },
        follower_triggers);

    REQUIRE(propagators.propagate(Literals{}, state, nullptr));
    CHECK(state.upper_bound(x) == 2_i);
    CHECK(state.upper_bound(y) == 7_i);

    // Round 1: both run (claimant caps x at 5, follower caps y at 7). The
    // claimant's x-inference wakes only the follower; the follower's
    // y-inference re-wakes the claimant. Round 2: follower finds nothing,
    // claimant caps x at 2. Round 3: only the follower is woken, and finds
    // nothing. Without the claim the claimant would also run a third time.
    CHECK(claimant_runs == 2);
    CHECK(follower_runs == 3);
}

TEST_CASE("A repeated trigger variable downgrades the claim")
{
    State state;
    Propagators propagators;
    auto x = state.allocate_integer_variable_with_state(0_i, 10_i);

    int runs = 0;
    Triggers triggers;
    triggers.on_change = {x, x};
    install_capping_propagator(propagators, x, triggers, PropagatorState::EnableButIdempotent, runs);

    REQUIRE(propagators.propagate(Literals{}, state, nullptr));
    CHECK(state.upper_bound(x) == 5_i);
    // The ignored claim behaves exactly like Enable: the second run is the
    // self-requeued no-op.
    CHECK(runs == 2);
}

TEST_CASE("A view aliasing another trigger variable downgrades the claim")
{
    State state;
    Propagators propagators;
    auto x = state.allocate_integer_variable_with_state(0_i, 10_i);

    int runs = 0;
    Triggers triggers;
    triggers.on_change = {x, -x + 3_i};
    install_capping_propagator(propagators, x, triggers, PropagatorState::EnableButIdempotent, runs);

    REQUIRE(propagators.propagate(Literals{}, state, nullptr));
    CHECK(state.upper_bound(x) == 5_i);
    CHECK(runs == 2);
}

TEST_CASE("A view of a distinct variable does not downgrade the claim")
{
    State state;
    Propagators propagators;
    auto x = state.allocate_integer_variable_with_state(0_i, 10_i);
    auto y = state.allocate_integer_variable_with_state(0_i, 10_i);

    int runs = 0;
    Triggers triggers;
    triggers.on_change = {x, -y + 3_i};
    install_capping_propagator(propagators, x, triggers, PropagatorState::EnableButIdempotent, runs);

    REQUIRE(propagators.propagate(Literals{}, state, nullptr));
    CHECK(state.upper_bound(x) == 5_i);
    CHECK(runs == 1);
}
