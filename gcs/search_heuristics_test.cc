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

#include <algorithm>
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

    Stats stats;

    Propagators propagators{stats};
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

    Stats stats;

    Propagators propagators{stats};
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

    Stats stats;

    Propagators propagators{stats};
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
    Stats stats;
    Propagators propagators{stats};

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
        for (auto && cond : generate(state.current(), propagators, x))
            yielded.push_back(cond);

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

// Every position-based value order used to materialise the domain, or walk to
// its chosen position one value at a time, and index into it. Asking the
// domain's interval set for the value at that position instead (issue #879)
// has to agree exactly, holes and all: a split point that lands somewhere else
// silently changes the shape of every search tree, and one that lands in a hole
// is not a value the variable can take.
namespace
{
    auto values_of(const CurrentState & s, IntegerVariableID var) -> vector<Integer>
    {
        vector<Integer> result;
        for (auto v : s.each_value(var))
            result.push_back(v);
        return result;
    }

    auto conditions_from(const BranchValueGenerator & generate, const CurrentState & s, const Propagators & p, IntegerVariableID var)
        -> vector<IntegerVariableCondition>
    {
        vector<IntegerVariableCondition> result;
        for (auto && cond : generate(s, p, var))
            result.push_back(cond);
        return result;
    }
}

TEST_CASE("Position-based value orders agree with enumerating the domain")
{
    // Shapes chosen so that the answer differs from lower() + position: a hole
    // straddling the midpoint, a hole either side of it, and single-value
    // intervals where every step crosses a gap. The contiguous case is in there
    // too, as the control.
    auto holes = GENERATE(vector<Integer>{}, vector<Integer>{5_i}, vector<Integer>{2_i, 3_i, 4_i}, vector<Integer>{8_i, 9_i},
        vector<Integer>{2_i, 4_i, 6_i, 8_i}, vector<Integer>{1_i, 2_i, 3_i, 7_i, 8_i, 9_i});

    State state;
    auto x = IntegerVariableID{state.allocate_integer_variable_with_state(0_i, 10_i)};
    for (const auto & h : holes)
        REQUIRE(Inference::Instantiated != state.infer_not_equal(x, h));

    Stats stats;
    Propagators propagators{stats};
    auto current = state.current();
    auto values = values_of(current, x);
    REQUIRE(values.size() >= 3);

    // The definitions these heuristics had before they became interval queries.
    auto split_at = values.at(values.size() / 2 - 1);
    auto median_at = values.at(values.size() / 2);

    CHECK(conditions_from(value_order::split_smallest_first(), current, propagators, x) ==
        vector<IntegerVariableCondition>{x <= split_at, x > split_at});
    CHECK(conditions_from(value_order::split_largest_first(), current, propagators, x) ==
        vector<IntegerVariableCondition>{x > split_at, x <= split_at});
    CHECK(conditions_from(value_order::median(), current, propagators, x) == vector<IntegerVariableCondition>{x == median_at, x != median_at});

    // split_random picks one of the two orderings, but always about the same point.
    auto split = conditions_from(value_order::split_random(7), current, propagators, x);
    REQUIRE(split.size() == 2);
    CHECK(((split[0] == (x <= split_at) && split[1] == (x > split_at)) || (split[0] == (x > split_at) && split[1] == (x <= split_at))));
}

TEST_CASE("Random value orders only ever draw a value the variable can take")
{
    // A position drawn uniformly used to index a vector of the domain's values,
    // so it could not name a hole. nth_value() has to keep that property: a
    // branch on x == v for a v not in the domain is an immediately failed
    // subtree, and on x != v it is a wasted one.
    State state;
    auto x = IntegerVariableID{state.allocate_integer_variable_with_state(0_i, 20_i)};
    for (auto h : {1_i, 2_i, 3_i, 7_i, 11_i, 12_i, 13_i, 14_i, 19_i})
        REQUIRE(Inference::Instantiated != state.infer_not_equal(x, h));

    Stats stats;
    Propagators propagators{stats};
    auto current = state.current();
    auto generate_out = value_order::random_out(99), generate_reject = value_order::reject_random_interval(99);

    for (int draw = 0; draw < 200; ++draw) {
        auto out = conditions_from(generate_out, current, propagators, x);
        REQUIRE(out.size() == 2);
        CHECK(current.in_domain(x, out[0].value));

        // reject_random_interval yields a range whose two ends are both drawn
        // positions, so both have to be values; the interior may be holes.
        auto reject = conditions_from(generate_reject, current, propagators, x);
        REQUIRE(reject.size() == 2);
        for (auto && cond : reject)
            CHECK(current.in_domain(x, cond.value));
    }
}

TEST_CASE("Position-based value orders do not walk the domain to find their value")
{
    // The property #879 is about. A domain this wide cannot be enumerated at
    // all, so a test that returns at once is itself the evidence; the audit lane
    // in large_domain_audit_test.cc pins the same thing against the guard.
    State state;
    auto x = IntegerVariableID{state.allocate_integer_variable_with_state(0_i, 1000000000_i)};
    // {0..10} u {500000000..1000000000}: 500000012 values, so position
    // 250000005 is the split point and 250000006 the median, both well inside
    // the upper interval.
    REQUIRE(Inference::Instantiated != state.infer_not_in_range(x, 11_i, 499999999_i));
    REQUIRE(state.domain_size(x) == 500000012_i);

    Stats stats;
    Propagators propagators{stats};
    auto current = state.current();

    auto split_at = 500000000_i + 250000005_i - 11_i;
    auto median_at = split_at + 1_i;
    CHECK(conditions_from(value_order::split_smallest_first(), current, propagators, x) ==
        vector<IntegerVariableCondition>{x <= split_at, x > split_at});
    CHECK(conditions_from(value_order::median(), current, propagators, x) == vector<IntegerVariableCondition>{x == median_at, x != median_at});

    auto out = conditions_from(value_order::random_out(5), current, propagators, x);
    REQUIRE(out.size() == 2);
    CHECK(current.in_domain(x, out[0].value));
}

TEST_CASE("Position-based value orders wired into solve_with find every solution")
{
    // Complete search over a domain with holes: which value a heuristic picks
    // only changes the order the tree is explored in, so all of them must still
    // enumerate the same solutions. The holes are the point --- an off-by-one in
    // a position query shows up here as a lost or repeated solution.
    auto which = GENERATE(0, 1, 2, 3, 4, 5);

    Problem problem;
    vector<IntegerVariableID> xs;
    for (int i = 0; i < 3; ++i)
        xs.push_back(problem.create_integer_variable(vector<Integer>{1_i, 2_i, 5_i, 8_i, 9_i}));
    for (unsigned i = 0; i < xs.size(); ++i)
        for (unsigned j = i + 1; j < xs.size(); ++j)
            problem.post(NotEquals{xs[i], xs[j]});
    problem.post(LessThan{xs[0], xs[2]});

    auto val = [&]() -> BranchValueGenerator {
        switch (which) {
        case 0: return value_order::split_smallest_first();
        case 1: return value_order::split_largest_first();
        case 2: return value_order::split_random(which + 1);
        case 3: return value_order::median();
        case 4: return value_order::random_out(which + 1);
        default: return value_order::reject_random_interval(which + 1);
        }
    }();

    int solutions = 0;
    solve_with(problem,
        SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                           ++solutions;
                           return true;
                       },
            .branch = branch_with(variable_order::dom(problem), val)});

    // 5 * 4 * 3 = 60 injective triples, halved by x[0] < x[2].
    CHECK(solutions == 30);
}

TEST_CASE("with_largest_value branches on the variable whose domain reaches highest")
{
    // Declared and documented in the header since it was written, but never
    // defined, so any caller got a link error; found by the large-domain
    // heuristic audit lane, which names every heuristic and so link-checks them.
    State state;
    auto a = IntegerVariableID{state.allocate_integer_variable_with_state(0_i, 5_i)};
    auto b = IntegerVariableID{state.allocate_integer_variable_with_state(0_i, 9_i)};
    auto c = IntegerVariableID{state.allocate_integer_variable_with_state(0_i, 7_i)};

    Problem dummy;
    Stats stats;
    Propagators propagators{stats};
    auto select = variable_order::with_largest_value(vector{a, b, c})(dummy, state, propagators);
    CHECK(select(state.current(), propagators) == b);

    auto smallest = variable_order::with_smallest_value(vector{a, b, c})(dummy, state, propagators);
    REQUIRE(Inference::Instantiated != state.infer_greater_than_or_equal(b, 3_i));
    CHECK(smallest(state.current(), propagators) == a);
}

TEST_CASE("Position-based value orders count positions from the smallest value of a view")
{
    // CurrentState::each_value() hands a *negated* view's values out in
    // descending order --- it applies the view to the underlying domain in
    // stored order, and negation reverses it --- where copy_of_values() sorts.
    // So the old "materialise each_value() and index it" spelling counted
    // positions from the top of a negated view's domain: median() picked the
    // wrong value for an even-sized domain, and split_smallest_first() cut so
    // that "var <= v" kept the *larger* part. The interval query counts from
    // lower(), which is what a position means.
    //
    // Nothing in the tree branches on a view today, so no proof moved when this
    // changed; the property is pinned here rather than left to that staying true.
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 5_i);
    auto var = IntegerVariableID{-x + 10_i}; // values 5..10, six of them
    Stats stats;
    Propagators propagators{stats};
    auto current = state.current();

    REQUIRE(current.domain_size(var) == 6_i);
    REQUIRE(current.lower_bound(var) == 5_i);
    REQUIRE(current.upper_bound(var) == 10_i);

    // Six values, so the lower half is 5..7 and the split point is 7. Counted
    // from the top --- what the old spelling did --- it would have been 8.
    CHECK(conditions_from(value_order::split_smallest_first(), current, propagators, var) == vector<IntegerVariableCondition>{var <= 7_i, var > 7_i});
    CHECK(conditions_from(value_order::split_largest_first(), current, propagators, var) == vector<IntegerVariableCondition>{var > 7_i, var <= 7_i});
    // Position 6 / 2 = 3, counting from 5, is 8. From the top it would be 7.
    CHECK(conditions_from(value_order::median(), current, propagators, var) == vector<IntegerVariableCondition>{var == 8_i, var != 8_i});
}

TEST_CASE("random is a permutation of the domain, drawn lazily")
{
    // It used to materialise the domain and shuffle it, which is O(width)
    // whether or not the search reads more than one value. Drawn a value at a
    // time instead (issue #879), it still has to be a permutation: every value
    // exactly once, or search is unsound one way and incomplete the other.
    State state;
    auto x = IntegerVariableID{state.allocate_integer_variable_with_state(0_i, 12_i)};
    for (auto h : {2_i, 3_i, 7_i, 11_i})
        REQUIRE(Inference::Instantiated != state.infer_not_equal(x, h));

    Stats stats;
    Propagators propagators{stats};
    auto current = state.current();
    auto expected = values_of(current, x);
    auto generate = value_order::random(31337);

    // Several draws, because a permutation bug can hide behind one lucky one.
    for (int draw = 0; draw < 50; ++draw) {
        vector<Integer> got;
        for (auto && cond : generate(current, propagators, x))
            got.push_back(cond.value);

        REQUIRE(got.size() == expected.size());
        auto sorted = got;
        std::sort(sorted.begin(), sorted.end());
        CHECK(sorted == expected);
    }
}

TEST_CASE("random does not enumerate a domain the search only reads the start of")
{
    // The laziness itself: a billion-value domain, of which the search takes
    // three values before descending. dev_docs/large-domains.md calls exactly
    // this legitimate for smallest_first; random now has the same property.
    State state;
    auto x = IntegerVariableID{state.allocate_integer_variable_with_state(0_i, 1000000000_i)};
    REQUIRE(Inference::Instantiated != state.infer_not_in_range(x, 11_i, 499999999_i));

    Stats stats;
    Propagators propagators{stats};
    auto current = state.current();

    vector<Integer> got;
    for (auto && cond : value_order::random(4)(current, propagators, x)) {
        got.push_back(cond.value);
        if (got.size() == 3)
            break;
    }

    REQUIRE(got.size() == 3);
    for (auto v : got)
        CHECK(current.in_domain(x, v));
    CHECK(got[0] != got[1]);
    CHECK(got[1] != got[2]);
    CHECK(got[0] != got[2]);
}

TEST_CASE("smallest_first and largest_first run the right way round on a negated view")
{
    // The symptom #890 was filed for. CurrentState::each_value() used to hand a
    // negated view's values out descending, so smallest_first() yielded the
    // largest first and was indistinguishable from largest_first(). These two
    // cannot use a position query --- they want the lazy generator, which is
    // exactly what makes them safe on a wide domain --- so the fix was to the
    // iteration order itself.
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 5_i);
    for (auto h : {1_i, 4_i})
        REQUIRE(Inference::Instantiated != state.infer_not_equal(x, h));
    // x is {0, 2, 3, 5}, so -x + 10 is {5, 7, 8, 10}.
    auto var = IntegerVariableID{-x + 10_i};
    Stats stats;
    Propagators propagators{stats};
    auto current = state.current();

    CHECK(conditions_from(value_order::smallest_first(), current, propagators, var) ==
        vector<IntegerVariableCondition>{var == 5_i, var == 7_i, var == 8_i, var == 10_i});
    CHECK(conditions_from(value_order::largest_first(), current, propagators, var) ==
        vector<IntegerVariableCondition>{var == 10_i, var == 8_i, var == 7_i, var == 5_i});

    // And the bound-reading pair still agree with them about which end is which.
    CHECK(conditions_from(value_order::smallest_in(), current, propagators, var)[0] == (var == 5_i));
    CHECK(conditions_from(value_order::largest_in(), current, propagators, var)[0] == (var == 10_i));
}
