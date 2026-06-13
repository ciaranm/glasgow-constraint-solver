#include <gcs/constraint.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/current_state.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>
#include <gcs/variable_id.hh>
#include <gcs/variable_weighting.hh>

#include <catch2/catch_test_macros.hpp>
#include <catch2/generators/catch_generators.hpp>

#include <optional>

using namespace gcs;
using namespace gcs::innards;

namespace
{
    auto a_propagator_that_does_nothing()
    {
        return [](const State &, auto &, ProofLogger * const) -> PropagatorState { return PropagatorState::Enable; };
    }
}

// dom_wdeg's setup only uses the Propagators (it ignores the Problem and State),
// so these tests drive it with a hand-built State + Propagators and an empty
// dummy Problem for the unused argument, which gives full control over domains,
// scopes, and weights.

TEST_CASE("dom_wdeg orders by dom/W, with a zero-weight variable last")
{
    Problem dummy;
    State state;
    auto a = state.allocate_integer_variable_with_state(0_i, 3_i); // dom 4
    auto b = state.allocate_integer_variable_with_state(0_i, 3_i); // dom 4
    auto c = state.allocate_integer_variable_with_state(0_i, 3_i); // dom 4
    auto d = state.allocate_integer_variable_with_state(0_i, 3_i); // dom 4, in no constraint
    auto x = state.allocate_integer_variable_with_state(0_i, 3_i);

    Propagators propagators;
    // a is in one constraint, b in two, c in three (each paired with x); weights
    // are uniform at the root, so W(a)=1, W(b)=2, W(c)=3 and W(d)=0.
    propagators.install(NumberedConstraint{1}, a_propagator_that_does_nothing(), Triggers{.on_change = {a, x}});
    propagators.install(NumberedConstraint{2}, a_propagator_that_does_nothing(), Triggers{.on_change = {b, x}});
    propagators.install(NumberedConstraint{3}, a_propagator_that_does_nothing(), Triggers{.on_change = {b, x}});
    propagators.install(NumberedConstraint{4}, a_propagator_that_does_nothing(), Triggers{.on_change = {c, x}});
    propagators.install(NumberedConstraint{5}, a_propagator_that_does_nothing(), Triggers{.on_change = {c, x}});
    propagators.install(NumberedConstraint{6}, a_propagator_that_does_nothing(), Triggers{.on_change = {c, x}});

    // dom/W: a=4/1=4, b=4/2=2, c=4/3 -> c is smallest.
    auto selector = variable_order::dom_wdeg({a, b, c})(dummy, state, propagators);
    auto picked = selector(state.current(), propagators);
    REQUIRE(picked.has_value());
    CHECK(*picked == IntegerVariableID{c});

    // d has weighted degree 0, so dom/W is infinite: it is least preferred and a
    // (finite ratio) wins.
    auto with_isolated = variable_order::dom_wdeg({d, a})(dummy, state, propagators);
    auto picked_isolated = with_isolated(state.current(), propagators);
    REQUIRE(picked_isolated.has_value());
    CHECK(*picked_isolated == IntegerVariableID{a});
}

TEST_CASE("dom_wdeg seeded weights change the choice")
{
    Problem dummy;
    State state;
    auto a = state.allocate_integer_variable_with_state(0_i, 3_i);
    auto b = state.allocate_integer_variable_with_state(0_i, 3_i);
    auto c = state.allocate_integer_variable_with_state(0_i, 3_i);
    auto x = state.allocate_integer_variable_with_state(0_i, 3_i);

    Propagators propagators;
    propagators.install(NumberedConstraint{1}, a_propagator_that_does_nothing(), Triggers{.on_change = {a, x}});
    propagators.install(NumberedConstraint{2}, a_propagator_that_does_nothing(), Triggers{.on_change = {b, x}});
    propagators.install(NumberedConstraint{3}, a_propagator_that_does_nothing(), Triggers{.on_change = {b, x}});
    propagators.install(NumberedConstraint{4}, a_propagator_that_does_nothing(), Triggers{.on_change = {c, x}});
    propagators.install(NumberedConstraint{5}, a_propagator_that_does_nothing(), Triggers{.on_change = {c, x}});
    propagators.install(NumberedConstraint{6}, a_propagator_that_does_nothing(), Triggers{.on_change = {c, x}});

    // Without a seed, c wins (as above). Seeding a's only constraint heavily
    // makes W(a)=10, so dom/W a=0.4 is now the smallest and a wins instead.
    WeightingState seed;
    seed.set_weight(NumberedConstraint{1}, 10.0);

    auto selector = variable_order::dom_wdeg({a, b, c}, WeightingScheme::Classic, seed)(dummy, state, propagators);
    auto picked = selector(state.current(), propagators);
    REQUIRE(picked.has_value());
    CHECK(*picked == IntegerVariableID{a});
}

TEST_CASE("dom_wdeg tie-breaks on degree")
{
    Problem dummy;
    State state;
    auto a = state.allocate_integer_variable_with_state(0_i, 3_i);
    auto b = state.allocate_integer_variable_with_state(0_i, 3_i);

    Propagators propagators;
    // Both share the single constraint, so W(a)=W(b)=1 and dom/W ties. But a is
    // registered on an extra trigger, giving it the higher degree, so the
    // tie-break prefers it.
    propagators.install(NumberedConstraint{1}, a_propagator_that_does_nothing(),
        Triggers{.on_change = {a, b}, .on_bounds = {a}});

    REQUIRE(propagators.degree_of(a) > propagators.degree_of(b));

    auto selector = variable_order::dom_wdeg({a, b})(dummy, state, propagators);
    auto picked = selector(state.current(), propagators);
    REQUIRE(picked.has_value());
    CHECK(*picked == IntegerVariableID{a});
}

TEST_CASE("dom_wdeg wired into solve_with finds every solution")
{
    // An all-different triangle over {1,2,3}: the six permutations. dom/wdeg only
    // changes branch order, so a complete search must still enumerate them all --
    // this exercises the whole wiring: selection via callbacks.branch, the
    // once-per-search setup in solve_with, and the conflict observer driving the
    // weights during search.
    auto scheme = GENERATE(WeightingScheme::Classic, WeightingScheme::CurrentArityCurrentDomain, WeightingScheme::ConflictHistorySearch);

    Problem problem;
    auto a = problem.create_integer_variable(1_i, 3_i);
    auto b = problem.create_integer_variable(1_i, 3_i);
    auto c = problem.create_integer_variable(1_i, 3_i);
    problem.post(NotEquals{a, b});
    problem.post(NotEquals{b, c});
    problem.post(NotEquals{a, c});

    int solutions = 0;
    solve_with(problem,
        SolveCallbacks{
            .solution = [&](const CurrentState &) -> bool { ++solutions; return true; },
            .branch = branch_with(variable_order::dom_wdeg(problem, scheme), value_order::smallest_first())});

    CHECK(solutions == 6);
}
