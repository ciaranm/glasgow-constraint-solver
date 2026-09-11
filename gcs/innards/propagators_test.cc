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
    Stats stats;
    Propagators propagators{stats};
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
    Stats stats;
    Propagators propagators{stats};
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
    Stats stats;
    Propagators propagators{stats};
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

TEST_CASE("A claimant is not re-woken by a foreign inference it had already seen")
{
    State state;
    Stats stats;
    Propagators propagators{stats};
    auto x = state.allocate_integer_variable_with_state(0_i, 10_i);
    auto y = state.allocate_integer_variable_with_state(0_i, 10_i);

    // The setter runs first (registration order) and caps y at 7.
    int setter_runs = 0;
    Triggers setter_triggers;
    setter_triggers.on_change = {y};
    propagators.install(
        ConstraintID{NumberedConstraint{1}},
        [&setter_runs, y](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            ++setter_runs;
            if (state.upper_bound(y) > 7_i)
                inference.infer(logger, y < 8_i, NoJustificationNeeded{}, NoReason{});
            return PropagatorState::Enable;
        },
        setter_triggers);

    // The claimant runs after the setter in the same round, so it has already
    // seen y's change when it acts on it; that change must not re-wake it.
    // Element-style, it does not watch the variable it writes.
    int claimant_runs = 0;
    Triggers claimant_triggers;
    claimant_triggers.on_change = {y};
    propagators.install(
        ConstraintID{NumberedConstraint{2}},
        [&claimant_runs, x, y](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            ++claimant_runs;
            if (state.upper_bound(y) <= 7_i && state.upper_bound(x) > 2_i)
                inference.infer(logger, x < 3_i, NoJustificationNeeded{}, NoReason{});
            return PropagatorState::EnableButIdempotent;
        },
        claimant_triggers);

    REQUIRE(propagators.propagate(Literals{}, state, nullptr));
    CHECK(state.upper_bound(x) == 2_i);
    CHECK(state.upper_bound(y) == 7_i);

    // Round 1: the setter caps y, then the claimant (which saw that) caps x.
    // The y-inference predates the claimant's run's end, so only the setter is
    // re-woken (by its own inference); round 2 finds nothing. Without the
    // already-seen rule the claimant would run a wasted second time.
    CHECK(setter_runs == 2);
    CHECK(claimant_runs == 1);
}

TEST_CASE("A claimant is re-woken by a foreign inference recorded after its run ended")
{
    State state;
    Stats stats;
    Propagators propagators{stats};
    auto x = state.allocate_integer_variable_with_state(0_i, 10_i);
    auto y = state.allocate_integer_variable_with_state(0_i, 10_i);

    // Same two propagators, but with the claimant registered first: in round
    // one it runs before the setter, finds nothing to do (y is still wide),
    // and claims; the setter's y-inference lands after the claimant's run
    // ended, so it must wake the claimant for round two.
    int claimant_runs = 0;
    Triggers claimant_triggers;
    claimant_triggers.on_change = {y};
    propagators.install(
        ConstraintID{NumberedConstraint{1}},
        [&claimant_runs, x, y](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            ++claimant_runs;
            if (state.upper_bound(y) <= 7_i && state.upper_bound(x) > 2_i)
                inference.infer(logger, x < 3_i, NoJustificationNeeded{}, NoReason{});
            return PropagatorState::EnableButIdempotent;
        },
        claimant_triggers);

    int setter_runs = 0;
    Triggers setter_triggers;
    setter_triggers.on_change = {y};
    propagators.install(
        ConstraintID{NumberedConstraint{2}},
        [&setter_runs, y](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            ++setter_runs;
            if (state.upper_bound(y) > 7_i)
                inference.infer(logger, y < 8_i, NoJustificationNeeded{}, NoReason{});
            return PropagatorState::Enable;
        },
        setter_triggers);

    REQUIRE(propagators.propagate(Literals{}, state, nullptr));
    CHECK(state.upper_bound(x) == 2_i);
    CHECK(state.upper_bound(y) == 7_i);

    // Round 1: claimant no-ops, setter caps y. Round 2: both re-run (the
    // claimant because y changed after its run ended -- even a no-op run's
    // claim only covers what it had seen), and the claimant caps x. Nobody
    // watches x, so round 3 is empty.
    CHECK(claimant_runs == 2);
    CHECK(setter_runs == 2);
}

TEST_CASE("A repeated trigger variable downgrades the claim")
{
    State state;
    Stats stats;
    Propagators propagators{stats};
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
    Stats stats;
    Propagators propagators{stats};
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
    Stats stats;
    Propagators propagators{stats};
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

// A refined watch is a one-shot subscription to a literal, and each inference is
// replayed to the wake machinery exactly once. So the round-boundary replay has
// to fire watches whichever path it takes: the claim-free one, or the one that
// gates coarse triggers on the already-seen rule. It did not, and because a
// dropped wake costs only pruning, nothing failed --- the tree just grew. It
// grew silently for the learned-nogood store, which is a watch client: refined
// took 259,103 recursions on `langford --size=11 --restarts=100` where the scan
// path it is meant to match took 258,670. And it grew catastrophically for the
// first client whose whole verdict rides on a watch --- reified equals against a
// constant, 767 nodes on nmseq/100 against 1,089,375 (issue #889).

namespace
{
    // Fires once: removes 7 from the middle of x's domain. Interior, so it is
    // exactly the granularity a `!= 7` watch subscribes to and a bounds trigger
    // would miss.
    auto install_hole_punching_propagator(Propagators & propagators, SimpleIntegerVariableID x, PropagatorState state_to_return, int & runs) -> void
    {
        Triggers triggers;
        triggers.on_change = {x};
        propagators.install(
            ConstraintID{NumberedConstraint{1}},
            [&runs, x, state_to_return](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                ++runs;
                if (state.in_domain(x, 7_i))
                    inference.infer(logger, x != 7_i, NoJustificationNeeded{}, NoReason{});
                return state_to_return;
            },
            triggers);
    }

    // Woken only by its watch: scope_only keeps x in scope (degree, adjacency)
    // while arming no coarse trigger, so a second run can only be the watch.
    auto install_watching_propagator(Propagators & propagators, SimpleIntegerVariableID x, int & runs) -> void
    {
        Triggers triggers;
        triggers.scope_only = {x};
        triggers.refined.emplace_back(x != 7_i, 0u);
        propagators.install(
            ConstraintID{NumberedConstraint{2}},
            [&runs](const State &, auto &, ProofLogger * const) -> PropagatorState {
                ++runs;
                return PropagatorState::Enable;
            },
            triggers);
    }
}

TEST_CASE("A refined watch fires when the round has an idempotence claimant")
{
    State state;
    Stats stats;
    Propagators propagators{stats};
    auto x = state.allocate_integer_variable_with_state(0_i, 10_i);

    int puncher_runs = 0, watcher_runs = 0;
    install_hole_punching_propagator(propagators, x, PropagatorState::EnableButIdempotent, puncher_runs);
    install_watching_propagator(propagators, x, watcher_runs);

    REQUIRE(propagators.propagate(Literals{}, state, nullptr));
    CHECK(! state.in_domain(x, 7_i));

    // Both run in the first pass, before the hole exists. The puncher's claim
    // sends the boundary down the already-seen path, which protects the puncher
    // from its own inference -- and must still fire the watcher's watch.
    CHECK(puncher_runs == 1);
    CHECK(watcher_runs == 2);
}

TEST_CASE("A refined watch fires when the round has no idempotence claimant")
{
    State state;
    Stats stats;
    Propagators propagators{stats};
    auto x = state.allocate_integer_variable_with_state(0_i, 10_i);

    int puncher_runs = 0, watcher_runs = 0;
    install_hole_punching_propagator(propagators, x, PropagatorState::Enable, puncher_runs);
    install_watching_propagator(propagators, x, watcher_runs);

    REQUIRE(propagators.propagate(Literals{}, state, nullptr));
    CHECK(! state.in_domain(x, 7_i));

    // The same wake, on the claim-free path: the watcher must not be able to
    // tell the two apart. The puncher re-runs here because its own inference
    // wakes it back through its coarse trigger.
    CHECK(puncher_runs == 2);
    CHECK(watcher_runs == 2);
}

// The round boundary asks once, before walking the round's inferences, whether the
// model has armed any watch at all, and replays through a body with the firing
// block compiled out when it has not (issue #895). That question has to be asked
// again at every boundary: a propagator can arm the model's very first watch in
// one round and need it fired at the next boundary of the same propagate() call,
// so an answer cached at entry to propagate() would drop it --- silently, since a
// lost wake costs only pruning.

namespace
{
    // Arms its first watch on its first run rather than at install, so the watch
    // index is empty when propagate() is entered and non-empty by the time the
    // boundary replays. scope_only keeps x in scope while arming no coarse
    // trigger, so any later run of it is its watch and nothing else.
    auto install_late_arming_propagator(Propagators & propagators, SimpleIntegerVariableID x, int & runs, int & payloads_seen) -> void
    {
        Triggers triggers;
        triggers.scope_only = {x};
        propagators.install(
            ConstraintID{NumberedConstraint{3}},
            [&runs, &payloads_seen, x](const State &, auto &, ProofLogger * const, const RefinedWatchContext & ctx) -> PropagatorState {
                ++runs;
                payloads_seen += static_cast<int>(ctx.fired_payloads().size());
                if (runs == 1)
                    ctx.watch(x != 7_i, 42u);
                return PropagatorState::Enable;
            },
            triggers);
    }
}

TEST_CASE("A watch armed during a round fires at that propagate()'s next boundary")
{
    State state;
    Stats stats;
    Propagators propagators{stats};
    auto x = state.allocate_integer_variable_with_state(0_i, 10_i);

    int arming_runs = 0, payloads_seen = 0, puncher_runs = 0;
    // Registration order is first-pass order: the arming propagator runs, and arms,
    // before the puncher makes the hole its watch is waiting for.
    install_late_arming_propagator(propagators, x, arming_runs, payloads_seen);
    install_hole_punching_propagator(propagators, x, PropagatorState::Enable, puncher_runs);

    REQUIRE(propagators.propagate(Literals{}, state, nullptr));
    CHECK(! state.in_domain(x, 7_i));

    CHECK(arming_runs == 2);
    CHECK(payloads_seen == 1);
}

// Propagators::shared_derived_data: the store that lets several constraints
// over one shared input derive something from it once between them. Keyed by
// (input address, type), created empty on the first ask, and the same object
// thereafter --- which is the whole of what a caller relies on, since it then
// fills the object in itself.

namespace
{
    struct Derived
    {
        int filled_in = 0;
    };

    struct OtherwiseDerived
    {
        int filled_in = 0;
    };
}

TEST_CASE("Shared derived data is shared between asks with the same key")
{
    Stats stats;
    Propagators propagators{stats};
    int input = 0;

    auto first = propagators.shared_derived_data<Derived>(&input);
    REQUIRE(first);
    CHECK(0 == first->filled_in);
    first->filled_in = 42;

    // The second constraint over the same input sees what the first left there,
    // rather than an empty one of its own.
    auto second = propagators.shared_derived_data<Derived>(&input);
    CHECK(second == first);
    CHECK(42 == second->filled_in);
}

TEST_CASE("Shared derived data is not shared between different inputs")
{
    Stats stats;
    Propagators propagators{stats};
    int input = 0, other_input = 0;

    auto first = propagators.shared_derived_data<Derived>(&input);
    auto second = propagators.shared_derived_data<Derived>(&other_input);
    CHECK(second != first);
    CHECK(0 == second->filled_in);
}

TEST_CASE("Shared derived data is not shared between different types")
{
    Stats stats;
    Propagators propagators{stats};
    int input = 0;

    // Two constraints deriving different things from one input get a slot each,
    // rather than the second one finding the first one's object under its own
    // type and failing the cast.
    auto first = propagators.shared_derived_data<Derived>(&input);
    first->filled_in = 42;
    auto second = propagators.shared_derived_data<OtherwiseDerived>(&input);
    CHECK(0 == second->filled_in);
    CHECK(42 == first->filled_in);
}
