#include <gcs/constraint.hh>
#include <gcs/constraints/comparison.hh>
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
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::vector;

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

    // dom/W: a=4/1=4, b=4/2=2, c=4/3 -> c is smallest. Use Classic explicitly:
    // it has uniform weights at the root, so this exercises the dom/W ratio
    // rather than the default scheme's particular starting point.
    auto selector = variable_order::dom_wdeg({a, b, c}, WeightingScheme::Classic)(dummy, state, propagators);
    auto picked = selector(state.current(), propagators);
    REQUIRE(picked.has_value());
    CHECK(*picked == IntegerVariableID{c});

    // d has weighted degree 0, so dom/W is infinite: it is least preferred and a
    // (finite ratio) wins.
    auto with_isolated = variable_order::dom_wdeg({d, a}, WeightingScheme::Classic)(dummy, state, propagators);
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
    // Both share the one binary constraint, so W(a)=W(b)=1 and dom/W ties. a is
    // also in a second, unary constraint: a unary constraint never has two
    // unassigned variables, so weighted_degree_of filters it out (W(a) stays 1),
    // but it still raises a's plain degree, so the degree tie-break prefers a.
    propagators.install(NumberedConstraint{1}, a_propagator_that_does_nothing(), Triggers{.on_change = {a, b}});
    propagators.install(NumberedConstraint{2}, a_propagator_that_does_nothing(), Triggers{.on_change = {a}});

    REQUIRE(propagators.degree_of(a) > propagators.degree_of(b));

    // Classic gives both the same weight, so the dom/W ratio ties and the
    // degree tie-break decides --- which is what this test checks.
    auto selector = variable_order::dom_wdeg({a, b}, WeightingScheme::Classic)(dummy, state, propagators);
    auto picked = selector(state.current(), propagators);
    REQUIRE(picked.has_value());
    CHECK(*picked == IntegerVariableID{a});
}

// split_random's coin flip used to yield the same pair of conditions in both
// arms, so it always took the upper half first: split_largest_first plus a
// wasted RNG draw (issue #568). Both orderings must appear, and every node
// must still offer exactly the complementary pair, or search stops being
// complete.
TEST_CASE("split_random takes each half first sometimes")
{
    State state;
    auto x = IntegerVariableID{state.allocate_integer_variable_with_state(1_i, 4_i)};
    Propagators propagators;

    // The split point does not depend on the coin flip: domain size 4 gives
    // mid = 2, and dropping mid - 1 = 1 value lands on 2 either way.
    const auto lower_half = x <= 2_i, upper_half = x > 2_i;

    // A fixed seed keeps this deterministic run to run. The exact sequence is
    // not portable --- uniform_int_distribution's algorithm is unspecified ---
    // but 100 draws from a fair coin see both arms on any implementation.
    auto generate = value_order::split_random(1234);

    bool saw_lower_first = false, saw_upper_first = false;
    for (int draw = 0; draw < 100; ++draw) {
        vector<IntegerVariableCondition> yielded;
        for (auto && decision : generate(state.current(), propagators, x))
            yielded.push_back(decision.guess);

        REQUIRE(yielded.size() == 2);
        if (yielded[0] == lower_half) {
            CHECK(yielded[1] == upper_half);
            saw_lower_first = true;
        }
        else {
            CHECK(yielded[0] == upper_half);
            CHECK(yielded[1] == lower_half);
            saw_upper_first = true;
        }
    }

    CHECK(saw_lower_first);
    CHECK(saw_upper_first);
}

TEST_CASE("split_random wired into solve_with finds every solution")
{
    // The 24 permutations of 1..4, restricted to the 12 with x[0] < x[3].
    // Which half of a domain is tried first only changes the order in which
    // the tree is explored, so a complete search must find all of them
    // whatever the coin flips do -- checked over several seeds, since each
    // seed gives a different sequence of branch orderings.
    auto seed = GENERATE(1, 2, 3, 4, 5);

    Problem problem;
    vector<IntegerVariableID> xs;
    for (int i = 0; i < 4; ++i)
        xs.push_back(problem.create_integer_variable(1_i, 4_i));
    for (unsigned i = 0; i < xs.size(); ++i)
        for (unsigned j = i + 1; j < xs.size(); ++j)
            problem.post(NotEquals{xs[i], xs[j]});
    problem.post(LessThan{xs[0], xs[3]});

    int solutions = 0;
    solve_with(problem,
        SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                           ++solutions;
                           return true;
                       },
            .branch = branch_with(variable_order::dom(problem), value_order::split_random(seed))});

    CHECK(solutions == 12);
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
        SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                           ++solutions;
                           return true;
                       },
            .branch = branch_with(variable_order::dom_wdeg(problem, scheme), value_order::smallest_first())});

    CHECK(solutions == 6);
}
