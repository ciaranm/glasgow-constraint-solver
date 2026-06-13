#include <gcs/constraint.hh>
#include <gcs/current_state.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>
#include <gcs/variable_id.hh>
#include <gcs/variable_weighting.hh>

#include <catch2/catch_approx.hpp>
#include <catch2/catch_test_macros.hpp>

#include <optional>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using Catch::Approx;
using std::nullopt;
using std::vector;

namespace
{
    // A do-nothing propagator, written fresh at each install site (the
    // PropagationFunction constructor wants the closure by value), to give a
    // constraint a scope without any real propagation behaviour.
    auto a_propagator_that_does_nothing()
    {
        return [](const State &, auto &, ProofLogger * const) -> PropagatorState { return PropagatorState::Enable; };
    }
}

TEST_CASE("ClassicDomWDeg starts at the variable's degree")
{
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 10_i);
    auto y = state.allocate_integer_variable_with_state(0_i, 10_i);
    auto z = state.allocate_integer_variable_with_state(0_i, 10_i);

    Propagators propagators;
    propagators.install(NumberedConstraint{1}, a_propagator_that_does_nothing(), Triggers{.on_change = {x, y}});
    propagators.install(NumberedConstraint{2}, a_propagator_that_does_nothing(), Triggers{.on_change = {y, z}});
    propagators.install(NumberedConstraint{3}, a_propagator_that_does_nothing(), Triggers{.on_change = {x, z}});

    ClassicDomWDeg weighting{propagators};
    auto current = state.current();

    // Every weight is 1 and every variable is unassigned, so weighted_degree_of
    // is just the number of constraints each variable is in.
    CHECK(weighting.weighted_degree_of(current, propagators, x) == 2.0);
    CHECK(weighting.weighted_degree_of(current, propagators, y) == 2.0);
    CHECK(weighting.weighted_degree_of(current, propagators, z) == 2.0);

    // A view resolves to its underlying variable; a constant is in no constraints.
    CHECK(weighting.weighted_degree_of(current, propagators, x + 1_i) == 2.0);
    CHECK(weighting.weighted_degree_of(current, propagators, constant_variable(4_i)) == 0.0);
}

TEST_CASE("ClassicDomWDeg bumps the failing constraint's weight")
{
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 10_i);
    auto y = state.allocate_integer_variable_with_state(0_i, 10_i);
    auto z = state.allocate_integer_variable_with_state(0_i, 10_i);

    Propagators propagators;
    propagators.install(NumberedConstraint{1}, a_propagator_that_does_nothing(), Triggers{.on_change = {x, y}});
    propagators.install(NumberedConstraint{2}, a_propagator_that_does_nothing(), Triggers{.on_change = {y, z}});
    propagators.install(NumberedConstraint{3}, a_propagator_that_does_nothing(), Triggers{.on_change = {x, z}});

    ClassicDomWDeg weighting{propagators};
    auto current = state.current();

    // Conflict on constraint _1 (dense index 0): w(_1) goes 1 -> 2.
    weighting.note_conflict(0, {}, nullopt, state);
    CHECK(weighting.weighted_degree_of(current, propagators, x) == 3.0); // w(_1)=2 + w(_3)=1
    CHECK(weighting.weighted_degree_of(current, propagators, y) == 3.0); // w(_1)=2 + w(_2)=1
    CHECK(weighting.weighted_degree_of(current, propagators, z) == 2.0); // w(_2)=1 + w(_3)=1, unchanged

    // Weights accumulate and are not tied to search state (no backtrack resets
    // them): a second conflict on _1 takes it to 3.
    weighting.note_conflict(0, {}, nullopt, state);
    CHECK(weighting.weighted_degree_of(current, propagators, x) == 4.0); // w(_1)=3 + w(_3)=1
}

TEST_CASE("ClassicDomWDeg counts only constraints with at least two unassigned variables")
{
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 10_i);
    auto y = state.allocate_integer_variable_with_state(5_i, 5_i); // already fixed
    auto z = state.allocate_integer_variable_with_state(0_i, 10_i);

    Propagators propagators;
    // _1 over {x, y}: y is fixed, so only one unassigned variable -> excluded.
    propagators.install(NumberedConstraint{1}, a_propagator_that_does_nothing(), Triggers{.on_change = {x, y}});
    // _2 over {x, z}: two unassigned -> counted.
    propagators.install(NumberedConstraint{2}, a_propagator_that_does_nothing(), Triggers{.on_change = {x, z}});

    ClassicDomWDeg weighting{propagators};
    auto current = state.current();

    CHECK(weighting.weighted_degree_of(current, propagators, x) == 1.0);

    // Even bumping the excluded constraint's weight does not change x's score,
    // because the |fut|>1 filter drops it.
    weighting.note_conflict(0, {}, nullopt, state);
    CHECK(weighting.weighted_degree_of(current, propagators, x) == 1.0);
}

TEST_CASE("ClassicDomWDeg snapshot and load round-trip")
{
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 10_i);
    auto y = state.allocate_integer_variable_with_state(0_i, 10_i);
    auto z = state.allocate_integer_variable_with_state(0_i, 10_i);

    Propagators propagators;
    propagators.install(NumberedConstraint{1}, a_propagator_that_does_nothing(), Triggers{.on_change = {x, y}});
    propagators.install(NumberedConstraint{2}, a_propagator_that_does_nothing(), Triggers{.on_change = {y, z}});
    propagators.install(NumberedConstraint{3}, a_propagator_that_does_nothing(), Triggers{.on_change = {x, z}});

    ClassicDomWDeg weighting{propagators};
    auto current = state.current();
    weighting.note_conflict(0, {}, nullopt, state); // w(_1)=2
    weighting.note_conflict(2, {}, nullopt, state); // w(_3)=2

    auto snap = weighting.snapshot(propagators);
    CHECK(snap.weight_of(NumberedConstraint{1}) == 2.0);
    CHECK(snap.weight_of(NumberedConstraint{2}) == 1.0);
    CHECK(snap.weight_of(NumberedConstraint{3}) == 2.0);
    // An identity not in the model has no weight.
    CHECK(snap.optional_weight_of(NamedConstraint{"absent"}) == nullopt);
    CHECK(snap.weight_of(NamedConstraint{"absent"}) == 0.0);

    // Loading the snapshot into a fresh weighting reproduces the scores.
    ClassicDomWDeg reloaded{propagators};
    reloaded.load(snap, propagators);
    CHECK(reloaded.weighted_degree_of(current, propagators, x) == weighting.weighted_degree_of(current, propagators, x));
    CHECK(reloaded.weighted_degree_of(current, propagators, y) == weighting.weighted_degree_of(current, propagators, y));
    CHECK(reloaded.weighted_degree_of(current, propagators, z) == weighting.weighted_degree_of(current, propagators, z));
}

TEST_CASE("WeightingState merge policies")
{
    WeightingState a;
    a.set_weight(NumberedConstraint{1}, 3.0);
    a.set_weight(NumberedConstraint{2}, 5.0);

    WeightingState b;
    b.set_weight(NumberedConstraint{2}, 1.0);
    b.set_weight(NumberedConstraint{3}, 7.0);

    SECTION("sum")
    {
        auto m = a;
        m.merge(b, WeightingState::MergePolicy::Sum);
        CHECK(m.weight_of(NumberedConstraint{1}) == 3.0); // only in a, unchanged
        CHECK(m.weight_of(NumberedConstraint{2}) == 6.0); // 5 + 1
        CHECK(m.weight_of(NumberedConstraint{3}) == 7.0); // 0 + 7
    }

    SECTION("max")
    {
        auto m = a;
        m.merge(b, WeightingState::MergePolicy::Max);
        CHECK(m.weight_of(NumberedConstraint{1}) == 3.0);
        CHECK(m.weight_of(NumberedConstraint{2}) == 5.0); // max(5, 1)
        CHECK(m.weight_of(NumberedConstraint{3}) == 7.0); // max(0, 7)
    }

    SECTION("average")
    {
        auto m = a;
        m.merge(b, WeightingState::MergePolicy::Average);
        CHECK(m.weight_of(NumberedConstraint{1}) == 3.0); // only in a, unchanged
        CHECK(m.weight_of(NumberedConstraint{2}) == 3.0); // (5 + 1) / 2
        CHECK(m.weight_of(NumberedConstraint{3}) == 3.5); // (0 + 7) / 2
    }
}

TEST_CASE("ConflictHistorySearch builds a recency-weighted score")
{
    State state;
    auto a = state.allocate_integer_variable_with_state(0_i, 10_i);
    auto b = state.allocate_integer_variable_with_state(0_i, 10_i);
    auto x = state.allocate_integer_variable_with_state(0_i, 10_i);

    Propagators propagators;
    propagators.install(NumberedConstraint{1}, a_propagator_that_does_nothing(), Triggers{.on_change = {a, x}});
    propagators.install(NumberedConstraint{2}, a_propagator_that_does_nothing(), Triggers{.on_change = {b, x}});

    ConflictHistorySearch weighting{propagators};
    auto current = state.current();

    // Before any conflict every q(c) = 0, so weighted_degree_of is just delta per
    // constraint (CHS orders by degree early on).
    CHECK(weighting.weighted_degree_of(current, propagators, a) == Approx(1.0e-4));

    // One conflict on _1: q(_1) = (1 - alpha) * 0 + alpha * r, with alpha = 0.4 and
    // r = 1 / (0 - 0 + 1) = 1, so q(_1) = 0.4. _2 is untouched.
    weighting.note_conflict(0, {}, nullopt, state);
    CHECK(weighting.weighted_degree_of(current, propagators, a) == Approx(0.4 + 1.0e-4));
    CHECK(weighting.weighted_degree_of(current, propagators, b) == Approx(1.0e-4));

    // A second conflict, now on _2, after one earlier conflict: its recency factor
    // r = 1 / (#Conflicts - Conflict(_2) + 1) = 1 / (1 - 0 + 1) = 0.5 is smaller,
    // so _2 ends up below _1.
    weighting.note_conflict(1, {}, nullopt, state);
    CHECK(weighting.weighted_degree_of(current, propagators, b) < weighting.weighted_degree_of(current, propagators, a));
}

TEST_CASE("ConflictHistorySearch snapshot and load round-trip the scores")
{
    State state;
    auto a = state.allocate_integer_variable_with_state(0_i, 10_i);
    auto x = state.allocate_integer_variable_with_state(0_i, 10_i);

    Propagators propagators;
    propagators.install(NumberedConstraint{1}, a_propagator_that_does_nothing(), Triggers{.on_change = {a, x}});

    ConflictHistorySearch weighting{propagators};
    auto current = state.current();
    weighting.note_conflict(0, {}, nullopt, state); // q(_1) = 0.4

    auto snap = weighting.snapshot(propagators);
    CHECK(snap.weight_of(NumberedConstraint{1}) == Approx(0.4));

    ConflictHistorySearch reloaded{propagators};
    reloaded.load(snap, propagators);
    CHECK(reloaded.weighted_degree_of(current, propagators, a) == Approx(weighting.weighted_degree_of(current, propagators, a)));
}
