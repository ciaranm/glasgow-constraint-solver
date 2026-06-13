#include <gcs/constraint.hh>
#include <gcs/innards/conflict_observer.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/justification.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>
#include <gcs/variable_id.hh>

#include <catch2/catch_test_macros.hpp>

#include <optional>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::nullopt;
using std::optional;
using std::vector;

namespace
{
    // Records every conflict it is told about, so a test can check which
    // constraint (and scope) a wipeout was attributed to.
    struct RecordingObserver final : ConflictObserver
    {
        struct Call
        {
            int constraint_index;
            vector<SimpleIntegerVariableID> scope;
            bool reason_present;
            bool reason_non_empty;
        };

        vector<Call> calls;

        auto note_conflict(int constraint_index, const vector<SimpleIntegerVariableID> & scope,
            const optional<ReasonFunction> & reason, const State &) -> void override
        {
            calls.push_back(Call{constraint_index, scope, reason.has_value(),
                reason.has_value() && static_cast<bool>(*reason)});
        }
    };

    // A do-nothing propagator, written as a fresh lambda at each install site
    // (the PropagationFunction constructor wants the closure by value), used as
    // an innocent bystander constraint that must not be blamed for a wipeout.
    auto a_propagator_that_does_nothing()
    {
        return [](const State &, auto &, ProofLogger * const) -> PropagatorState { return PropagatorState::Enable; };
    }
}

TEST_CASE("Conflict observer attributes a wipeout to the failing constraint, not a bystander")
{
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 1_i);
    auto y = state.allocate_integer_variable_with_state(0_i, 1_i);

    Propagators propagators;
    // Constraint _1: innocent, triggers on x only. Dense constraint index 0.
    propagators.install(NumberedConstraint{1}, a_propagator_that_does_nothing(), Triggers{.on_change = {x}});
    // Constraint _2: explicitly contradicts, with a non-empty reason. It is
    // registered second, so its propagator (id 1) runs after the bystander and
    // it gets dense constraint index 1. Its scope triggers on x and y, plus a
    // view of x (x + 1) that must resolve back to x and deduplicate away.
    propagators.install(
        NumberedConstraint{2},
        [x, y](const State & inner_state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            inference.contradiction(logger, JustifyUsingRUP{},
                generic_reason(inner_state, vector<IntegerVariableID>{x, y}));
        },
        Triggers{.on_change = {x, y}, .on_bounds = {x + 1_i}});

    RecordingObserver observer;
    propagators.set_conflict_observer(&observer);

    auto no_contradiction = propagators.propagate(nullopt, state, nullptr);

    CHECK_FALSE(no_contradiction);
    REQUIRE(observer.calls.size() == 1);

    const auto & call = observer.calls.front();
    // The blame falls on _2 (dense index 1), never on the bystander _1.
    CHECK(call.constraint_index == 1);
    CHECK(propagators.constraint_id_for_index(call.constraint_index) == ConstraintID{NumberedConstraint{2}});
    // Scope is the failing propagator's scope: x and y, with the x + 1 view
    // resolved and deduplicated.
    CHECK(call.scope == vector<SimpleIntegerVariableID>{x, y});
    // The reason was carried through, engaged and non-empty.
    CHECK(call.reason_present);
    CHECK(call.reason_non_empty);
}

TEST_CASE("Conflict observer fires for an inference-driven wipeout")
{
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 1_i);

    Propagators propagators;
    // The contradiction here comes not from an explicit contradiction() call but
    // from an inference that empties x's domain (the Contradiction case inside
    // the tracker), exercising the other reason-stash path.
    propagators.install(
        NumberedConstraint{7},
        [x](const State &, auto & inference, ProofLogger * const logger) -> PropagatorState {
            inference.infer_greater_than_or_equal(logger, x, 5_i, JustifyUsingRUP{}, ReasonFunction{});
            return PropagatorState::Enable;
        },
        Triggers{.on_bounds = {x}});

    RecordingObserver observer;
    propagators.set_conflict_observer(&observer);

    auto no_contradiction = propagators.propagate(nullopt, state, nullptr);

    CHECK_FALSE(no_contradiction);
    REQUIRE(observer.calls.size() == 1);

    const auto & call = observer.calls.front();
    CHECK(call.constraint_index == 0);
    CHECK(propagators.constraint_id_for_index(call.constraint_index) == ConstraintID{NumberedConstraint{7}});
    CHECK(call.scope == vector<SimpleIntegerVariableID>{x});
    // An empty ReasonFunction was supplied: the optional is engaged, but the
    // function it holds is empty.
    CHECK(call.reason_present);
    CHECK_FALSE(call.reason_non_empty);
}

TEST_CASE("Propagation without a conflict observer still detects the wipeout")
{
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 1_i);

    Propagators propagators;
    propagators.install(
        NumberedConstraint{1},
        [](const State &, auto & inference, ProofLogger * const logger) -> PropagatorState {
            inference.contradiction(logger, JustifyUsingRUP{}, ReasonFunction{});
        },
        Triggers{.on_change = {x}});

    // No observer attached: the propagate() notification is guarded and must not
    // be reached, but the contradiction is still reported.
    CHECK(propagators.conflict_observer() == nullptr);
    CHECK_FALSE(propagators.propagate(nullopt, state, nullptr));
}

TEST_CASE("Propagator scope and variable-to-constraint adjacency")
{
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 10_i);
    auto y = state.allocate_integer_variable_with_state(0_i, 10_i);
    auto z = state.allocate_integer_variable_with_state(0_i, 10_i);

    Propagators propagators;
    // Constraint index 0, propagator 0: over x and y (with a duplicate and a
    // view of y to check deduplication / view resolution).
    propagators.install(NumberedConstraint{1}, a_propagator_that_does_nothing(),
        Triggers{.on_change = {x, y}, .on_bounds = {y, -y}});
    // Constraint index 1, propagator 1: over y and z.
    propagators.install(NumberedConstraint{2}, a_propagator_that_does_nothing(),
        Triggers{.on_change = {y, z}});

    CHECK(propagators.scope_of_propagator(0) == vector<SimpleIntegerVariableID>{x, y});
    CHECK(propagators.scope_of_propagator(1) == vector<SimpleIntegerVariableID>{y, z});

    // x is only in constraint 0; y is in both; z is only in constraint 1.
    CHECK(propagators.constraint_indices_of_variable(x) == vector<int>{0});
    CHECK(propagators.constraint_indices_of_variable(y) == vector<int>{0, 1});
    CHECK(propagators.constraint_indices_of_variable(z) == vector<int>{1});

    // A variable no propagator triggers on has no constraints.
    auto unused = state.allocate_integer_variable_with_state(0_i, 0_i);
    CHECK(propagators.constraint_indices_of_variable(unused).empty());
}
