/* Propagators::install_with_optional_interior_pruning() and
 * analyse_optional_interior_pruning(): which variables' interior values each
 * propagator reads, and the least-fixpoint question of which optional prunings
 * something could observe. The first half drives the analysis with synthetic
 * propagators, which is the only way to reach every case (Element's own
 * conditional reads are all read unconditionally by its index propagator as
 * well, so it cannot exercise promotion on its own). The second half builds the
 * two constant-array Element models the analysis was designed around, qap and
 * tsp, and checks it says what issue #902 says it should. */

#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/circuit.hh>
#include <gcs/constraints/element.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/exception.hh>
#include <gcs/expression.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/justification.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>
#include <gcs/problem.hh>
#include <gcs/search_heuristics.hh>
#include <gcs/solve.hh>
#include <gcs/stats.hh>
#include <gcs/variable_id.hh>

#include <catch2/catch_test_macros.hpp>

#include <optional>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::optional;
using std::pair;
using std::string;
using std::vector;

namespace
{
    // A propagator that never does anything. Only its triggers matter to the
    // analysis. A fresh lambda each time, since PropagationFunction takes the
    // closure by value.
    auto does_nothing()
    {
        return [](const State &, auto &, ProofLogger * const) -> PropagatorState { return PropagatorState::Enable; };
    }

    // Installs an optional pruning of `targets` for `constraint`, whose pruning
    // propagator reads the interiors of `pruning_reads` and whose fallback reads
    // only the bounds of `targets` unless told otherwise.
    auto install_pair(Propagators & propagators, unsigned long long constraint, const vector<IntegerVariableID> & targets,
        const vector<IntegerVariableID> & pruning_reads, const vector<IntegerVariableID> & fallback_reads = {}) -> void
    {
        Triggers pruning_triggers{.on_change = pruning_reads, .on_bounds = targets};
        Triggers fallback_triggers{.on_change = fallback_reads, .on_bounds = targets};
        propagators.install_with_optional_interior_pruning(
            NumberedConstraint{constraint}, targets, does_nothing(), pruning_triggers, does_nothing(), fallback_triggers);
    }

    auto verdict_for(const vector<OptionalInteriorPruningVerdict> & verdicts, unsigned long long constraint)
        -> optional<OptionalInteriorPruningVerdict>
    {
        for (const auto & v : verdicts)
            if (v.constraint_id == ConstraintID{NumberedConstraint{constraint}})
                return v;
        return std::nullopt;
    }

    auto needed(const Propagators & propagators, unsigned long long constraint) -> bool
    {
        auto v = verdict_for(propagators.analyse_optional_interior_pruning(), constraint);
        REQUIRE(v);
        return v->needed;
    }
}

TEST_CASE("An optional pruning nothing else reads is not needed")
{
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 9_i);
    Stats stats;
    Propagators propagators{stats};

    install_pair(propagators, 1, {x}, {});
    // Another constraint that reads only x's bounds, or only whether it is
    // fixed, cannot observe an interior value.
    propagators.install(NumberedConstraint{2}, does_nothing(), Triggers{.on_bounds = {x}});
    propagators.install(NumberedConstraint{3}, does_nothing(), Triggers{.on_instantiated = {x}});

    auto verdicts = propagators.analyse_optional_interior_pruning();
    REQUIRE(verdicts.size() == 1);
    CHECK(verdicts.at(0).constraint_id == ConstraintID{NumberedConstraint{1}});
    CHECK(verdicts.at(0).targets == vector<SimpleIntegerVariableID>{x});
    CHECK_FALSE(verdicts.at(0).needed);
    CHECK_FALSE(verdicts.at(0).observed_by);
}

TEST_CASE("Another constraint reading a target's interior makes the pruning needed")
{
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 9_i);
    Stats stats;
    Propagators propagators{stats};

    install_pair(propagators, 1, {x}, {});
    propagators.install(NumberedConstraint{2}, does_nothing(), Triggers{.on_change = {x}});

    auto v = verdict_for(propagators.analyse_optional_interior_pruning(), 1);
    REQUIRE(v);
    CHECK(v->needed);
    CHECK(v->observed_by == optional<ConstraintID>{NumberedConstraint{2}});
}

TEST_CASE("A constraint's own reads of its targets do not make its pruning needed")
{
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 9_i);
    Stats stats;
    Propagators propagators{stats};

    // Element's shape: an always-on propagator of the same constraint reads the
    // target's interior. That is exempt; the pair's declaration promises it
    // cannot tell the difference.
    propagators.install(NumberedConstraint{1}, does_nothing(), Triggers{.on_change = {x}});
    install_pair(propagators, 1, {x}, {x});
    CHECK_FALSE(needed(propagators, 1));
}

TEST_CASE("Interior reads are derived from the triggers")
{
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 9_i);
    Stats stats;

    SECTION("scope_only counts, since the propagator arranges its own wakes")
    {
        Propagators propagators{stats};
        install_pair(propagators, 1, {x}, {});
        propagators.install(NumberedConstraint{2}, does_nothing(), Triggers{.scope_only = {x}});
        CHECK(needed(propagators, 1));
    }

    SECTION("a refined watch on a disequality counts")
    {
        Propagators propagators{stats};
        install_pair(propagators, 1, {x}, {});
        propagators.install(NumberedConstraint{2}, does_nothing(), Triggers{.refined = {{x != 3_i, 0u}}});
        CHECK(needed(propagators, 1));
    }

    SECTION("a refined watch on an equality counts")
    {
        Propagators propagators{stats};
        install_pair(propagators, 1, {x}, {});
        propagators.install(NumberedConstraint{2}, does_nothing(), Triggers{.refined = {{x == 3_i, 0u}}});
        CHECK(needed(propagators, 1));
    }

    SECTION("a refined watch on a bound does not")
    {
        Propagators propagators{stats};
        install_pair(propagators, 1, {x}, {});
        propagators.install(NumberedConstraint{2}, does_nothing(), Triggers{.refined = {{x >= 3_i, 0u}, {x < 7_i, 1u}}});
        CHECK_FALSE(needed(propagators, 1));
    }
}

TEST_CASE("Triggers::interior_reads overrides what the triggers say")
{
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 9_i);
    Stats stats;

    SECTION("an empty list: woken on any change, but reading only bounds")
    {
        Propagators propagators{stats};
        install_pair(propagators, 1, {x}, {});
        propagators.install(NumberedConstraint{2}, does_nothing(), Triggers{.on_change = {x}, .interior_reads = vector<IntegerVariableID>{}});
        CHECK_FALSE(needed(propagators, 1));
    }

    SECTION("an explicit read of a variable only watched for its bounds")
    {
        Propagators propagators{stats};
        install_pair(propagators, 1, {x}, {});
        propagators.install(NumberedConstraint{2}, does_nothing(), Triggers{.on_bounds = {x}, .interior_reads = vector<IntegerVariableID>{x}});
        CHECK(needed(propagators, 1));
    }
}

TEST_CASE("Views resolve to their underlying variable, and constants have no interior")
{
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 9_i);
    Stats stats;

    SECTION("a reader of a view of a target")
    {
        Propagators propagators{stats};
        install_pair(propagators, 1, {x}, {});
        propagators.install(NumberedConstraint{2}, does_nothing(), Triggers{.on_change = {-x + 3_i}});
        CHECK(needed(propagators, 1));
    }

    SECTION("a target that is a view")
    {
        Propagators propagators{stats};
        install_pair(propagators, 1, {x + 1_i}, {});
        propagators.install(NumberedConstraint{2}, does_nothing(), Triggers{.on_change = {x}});
        auto v = verdict_for(propagators.analyse_optional_interior_pruning(), 1);
        REQUIRE(v);
        CHECK(v->targets == vector<SimpleIntegerVariableID>{x});
        CHECK(v->needed);
    }

    SECTION("a constant target")
    {
        Propagators propagators{stats};
        install_pair(propagators, 1, {constant_variable(4_i)}, {});
        propagators.install(NumberedConstraint{2}, does_nothing(), Triggers{.on_change = {x}});
        auto v = verdict_for(propagators.analyse_optional_interior_pruning(), 1);
        REQUIRE(v);
        CHECK(v->targets.empty());
        CHECK_FALSE(v->needed);
    }
}

TEST_CASE("Permanently disabled propagators read nothing")
{
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 9_i);
    Stats stats;

    SECTION("a retired reader")
    {
        Propagators propagators{stats};
        install_pair(propagators, 1, {x}, {});
        propagators.install(NumberedConstraint{2}, does_nothing(), Triggers{.on_change = {x}});
        vector<ConstraintID> retire{NumberedConstraint{2}};
        propagators.disable_propagators_for_constraints(retire);
        CHECK_FALSE(needed(propagators, 1));
    }

    SECTION("a retired pair is not reported, and its fallback's reads do not count")
    {
        Propagators propagators{stats};
        install_pair(propagators, 1, {x}, {}, {x});
        auto y = state.allocate_integer_variable_with_state(0_i, 9_i);
        install_pair(propagators, 2, {x}, {});
        vector<ConstraintID> retire{NumberedConstraint{1}};
        propagators.disable_propagators_for_constraints(retire);
        auto verdicts = propagators.analyse_optional_interior_pruning();
        REQUIRE(verdicts.size() == 1);
        CHECK(verdicts.at(0).constraint_id == ConstraintID{NumberedConstraint{2}});
        CHECK_FALSE(verdicts.at(0).needed);
        (void)y;
    }
}

TEST_CASE("A needed pruning's own reads promote further pruning")
{
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 9_i);
    auto y = state.allocate_integer_variable_with_state(0_i, 9_i);
    auto z = state.allocate_integer_variable_with_state(0_i, 9_i);
    Stats stats;
    Propagators propagators{stats};

    // 1 prunes x, and reads y's interior only when it does; 2 prunes y, reading
    // z's; 3 prunes z. Nothing reads x yet, so nothing is needed.
    install_pair(propagators, 1, {x}, {y});
    install_pair(propagators, 2, {y}, {z});
    install_pair(propagators, 3, {z}, {});
    auto verdicts = propagators.analyse_optional_interior_pruning();
    CHECK_FALSE(verdict_for(verdicts, 1)->needed);
    CHECK_FALSE(verdict_for(verdicts, 2)->needed);
    CHECK_FALSE(verdict_for(verdicts, 3)->needed);

    // Now something reads x, and the whole chain switches on, each link blamed
    // on the one before it.
    propagators.install(NumberedConstraint{4}, does_nothing(), Triggers{.on_change = {x}});
    verdicts = propagators.analyse_optional_interior_pruning();
    CHECK(verdict_for(verdicts, 1)->observed_by == optional<ConstraintID>{NumberedConstraint{4}});
    CHECK(verdict_for(verdicts, 2)->observed_by == optional<ConstraintID>{NumberedConstraint{1}});
    CHECK(verdict_for(verdicts, 3)->observed_by == optional<ConstraintID>{NumberedConstraint{2}});
}

TEST_CASE("A cycle of prunings that nothing else reaches stays off")
{
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 9_i);
    auto y = state.allocate_integer_variable_with_state(0_i, 9_i);
    Stats stats;

    // Each could observe the other, so switching off whatever nothing reads,
    // starting with both on, would keep both. The least fixpoint has both off.
    SECTION("unreached")
    {
        Propagators propagators{stats};
        install_pair(propagators, 1, {x}, {y});
        install_pair(propagators, 2, {y}, {x});
        auto verdicts = propagators.analyse_optional_interior_pruning();
        CHECK_FALSE(verdict_for(verdicts, 1)->needed);
        CHECK_FALSE(verdict_for(verdicts, 2)->needed);
    }

    SECTION("reached")
    {
        Propagators propagators{stats};
        install_pair(propagators, 1, {x}, {y});
        install_pair(propagators, 2, {y}, {x});
        propagators.install(NumberedConstraint{3}, does_nothing(), Triggers{.on_change = {y}});
        auto verdicts = propagators.analyse_optional_interior_pruning();
        CHECK(verdict_for(verdicts, 2)->observed_by == optional<ConstraintID>{NumberedConstraint{3}});
        CHECK(verdict_for(verdicts, 1)->observed_by == optional<ConstraintID>{NumberedConstraint{2}});
    }
}

TEST_CASE("A fallback's reads count whether or not its pruning is needed")
{
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 9_i);
    auto y = state.allocate_integer_variable_with_state(0_i, 9_i);
    Stats stats;
    Propagators propagators{stats};

    install_pair(propagators, 1, {x}, {});
    install_pair(propagators, 2, {y}, {}, {x});
    auto verdicts = propagators.analyse_optional_interior_pruning();
    CHECK(verdict_for(verdicts, 1)->observed_by == optional<ConstraintID>{NumberedConstraint{2}});
    CHECK_FALSE(verdict_for(verdicts, 2)->needed);
}

TEST_CASE("Until something chooses, a pair propagates as its pruning propagator alone")
{
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 9_i);
    Stats stats;
    Propagators propagators{stats};

    // The pruning removes an interior value; the fallback, which must not run,
    // would move a bound.
    propagators.install_with_optional_interior_pruning(
        NumberedConstraint{1}, {x},
        [x](const State &, auto & inference, ProofLogger * const logger) -> PropagatorState {
            inference.infer(logger, x != 4_i, JustifyUsingRUP{}, NoReason{});
            return PropagatorState::Enable;
        },
        Triggers{.on_change = {x}},
        [x](const State &, auto & inference, ProofLogger * const logger) -> PropagatorState {
            inference.infer(logger, x < 8_i, JustifyUsingRUP{}, NoReason{});
            return PropagatorState::Enable;
        },
        Triggers{.on_bounds = {x}});

    REQUIRE(propagators.propagate(Literals{}, state, nullptr));
    // One propagator id for the pair.
    CHECK(propagators.number_of_propagators() == 1);
    CHECK_FALSE(state.in_domain(x, 4_i));
    CHECK(state.upper_bound(x) == 9_i);
}

TEST_CASE("A pair's propagators must use coarse triggers only")
{
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 9_i);
    Stats stats;
    Propagators propagators{stats};

    // A refined watch is delivered to a propagator id, which the two share.
    CHECK_THROWS_AS(propagators.install_with_optional_interior_pruning(
                        NumberedConstraint{1}, {x}, does_nothing(), Triggers{.refined = {{x != 3_i, 0u}}}, does_nothing(), Triggers{}),
        UnexpectedException);
    CHECK_THROWS_AS(propagators.install_with_optional_interior_pruning(
                        NumberedConstraint{1}, {x}, does_nothing(), Triggers{}, does_nothing(), Triggers{.refined = {{x >= 3_i, 0u}}}),
        UnexpectedException);
}

namespace
{
    // A pair on x whose pruning removes the interior value 4 and whose fallback
    // moves the upper bound to 7, so that which one ran is visible afterwards.
    auto install_visible_pair(Propagators & propagators, unsigned long long constraint, IntegerVariableID x) -> void
    {
        propagators.install_with_optional_interior_pruning(
            NumberedConstraint{constraint}, {x},
            [x](const State &, auto & inference, ProofLogger * const logger) -> PropagatorState {
                inference.infer(logger, x != 4_i, JustifyUsingRUP{}, NoReason{});
                return PropagatorState::Enable;
            },
            Triggers{.on_change = {x}},
            [x](const State &, auto & inference, ProofLogger * const logger) -> PropagatorState {
                inference.infer(logger, x < 8_i, JustifyUsingRUP{}, NoReason{});
                return PropagatorState::Enable;
            },
            Triggers{.on_bounds = {x}});
    }

    enum class Ran
    {
        Pruning,
        Fallback
    };

    auto which_ran(Propagators & propagators, State & state, IntegerVariableID x) -> Ran
    {
        auto timestamp = state.new_epoch();
        REQUIRE(propagators.propagate(Literals{}, state, nullptr));
        auto pruned = ! state.in_domain(x, 4_i);
        auto fell_back = state.upper_bound(x) == 7_i;
        state.backtrack(timestamp);
        REQUIRE(pruned != fell_back);
        return pruned ? Ran::Pruning : Ran::Fallback;
    }
}

TEST_CASE("Choosing switches an unneeded pair to its fallback, and keeps a needed one")
{
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 9_i);
    Stats stats;
    Propagators propagators{stats};
    install_visible_pair(propagators, 1, x);

    CHECK(which_ran(propagators, state, x) == Ran::Pruning);
    auto verdicts = propagators.choose_optional_interior_pruning();
    REQUIRE(verdicts.size() == 1);
    CHECK_FALSE(verdicts.at(0).needed);
    CHECK(which_ran(propagators, state, x) == Ran::Fallback);

    // Something that reads x's interior arrives later: choosing again puts
    // the pruning back.
    propagators.install(NumberedConstraint{2}, does_nothing(), Triggers{.on_change = {x}});
    verdicts = propagators.choose_optional_interior_pruning();
    REQUIRE(verdicts.size() == 1);
    CHECK(verdicts.at(0).needed);
    CHECK(which_ran(propagators, state, x) == Ran::Pruning);

    // And choosing again changes nothing.
    propagators.choose_optional_interior_pruning();
    CHECK(which_ran(propagators, state, x) == Ran::Pruning);
}

TEST_CASE("Choosing leaves a retired pair retired")
{
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 9_i);
    Stats stats;
    Propagators propagators{stats};
    install_visible_pair(propagators, 1, x);
    vector<ConstraintID> retire{NumberedConstraint{1}};
    propagators.disable_propagators_for_constraints(retire);

    CHECK(propagators.choose_optional_interior_pruning().empty());
    REQUIRE(propagators.propagate(Literals{}, state, nullptr));
    CHECK(state.in_domain(x, 4_i));
    CHECK(state.upper_bound(x) == 9_i);
}

TEST_CASE("Choosing reports what it decided")
{
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 9_i);
    auto y = state.allocate_integer_variable_with_state(0_i, 9_i);
    Stats stats;
    stats.set_report_handler(silent_stats_report());
    Propagators propagators{stats};
    install_visible_pair(propagators, 1, x);
    install_visible_pair(propagators, 2, y);
    propagators.install(NumberedConstraint{3}, does_nothing(), Triggers{.on_change = {y}});
    propagators.choose_optional_interior_pruning();

    vector<StatsNote> general, detailed;
    for (const auto & note : stats.notes()) {
        if (note.level == StatsLevel::General)
            general.push_back(note);
        else if (note.level == StatsLevel::Detailed)
            detailed.push_back(note);
    }
    REQUIRE(general.size() == 1);
    CHECK(general.at(0).text.find("switched 1 of 2") != string::npos);
    REQUIRE(detailed.size() == 1);
    CHECK(detailed.at(0).constraint == optional<ConstraintID>{NumberedConstraint{2}});
    CHECK(detailed.at(0).text.find("_3") != string::npos);
}

TEST_CASE("A pair counts once towards degree, over the union of its scopes")
{
    State state;
    auto x = state.allocate_integer_variable_with_state(0_i, 9_i);
    auto y = state.allocate_integer_variable_with_state(0_i, 9_i);
    auto z = state.allocate_integer_variable_with_state(0_i, 9_i);
    Stats stats;
    Propagators propagators{stats};

    // x is in both scopes, y only the pruning's, z only the fallback's.
    propagators.install_with_optional_interior_pruning(
        NumberedConstraint{1}, {x}, does_nothing(), Triggers{.on_change = {x, y}}, does_nothing(), Triggers{.on_bounds = {x, z}});
    CHECK(propagators.degree_of(x) == 1);
    CHECK(propagators.degree_of(y) == 1);
    CHECK(propagators.degree_of(z) == 1);
}

namespace
{
    // The verdicts for every Element in a model, keyed by nothing in particular:
    // the tests below only ever want "all of them" or "the one on this result".
    auto analyse(const Problem & p) -> pair<Propagators, vector<OptionalInteriorPruningVerdict>>
    {
        static Stats stats;
        auto state = p.create_state_for_new_search(nullptr);
        auto propagators = p.create_propagators(state, stats, nullptr);
        auto verdicts = propagators.analyse_optional_interior_pruning();
        return pair{std::move(propagators), std::move(verdicts)};
    }

    auto verdict_on(const vector<OptionalInteriorPruningVerdict> & verdicts, IntegerVariableID result) -> optional<OptionalInteriorPruningVerdict>
    {
        auto s = std::get<SimpleIntegerVariableID>(result);
        for (const auto & v : verdicts)
            if (v.targets == vector<SimpleIntegerVariableID>{s})
                return v;
        return std::nullopt;
    }
}

TEST_CASE("qap: nothing can observe an element result's interior")
{
    // The shape of minicp_benchmarks/qap at size 4: every pairwise distance
    // d_ij = D[x_i][x_j] feeds a single weighted sum, which is the objective.
    const int size = 4;
    vector<vector<Integer>> distances{{0_i, 3_i, 7_i, 2_i}, {3_i, 0_i, 5_i, 9_i}, {7_i, 5_i, 0_i, 4_i}, {2_i, 9_i, 4_i, 0_i}};

    Problem p;
    auto xs = p.create_integer_variable_vector(size, 0_i, Integer{size - 1}, "xs");
    for (int i = 0; i < size; ++i)
        for (int j = i + 1; j < size; ++j)
            p.post(NotEquals{xs[i], xs[j]});

    WeightedSum wcosts;
    vector<IntegerVariableID> ds;
    for (int i = 0; i < size; ++i)
        for (int j = 0; j < size; ++j) {
            auto d = p.create_integer_variable(0_i, 10_i);
            p.post(Element2DConstantArray{d, xs[i], xs[j], &distances}.with_consistency(consistency::Auto{}));
            wcosts += Integer{i + j + 1} * d;
            ds.push_back(d);
        }
    auto cost = p.create_integer_variable(0_i, 100000_i, "cost");
    p.post(std::move(wcosts) == 1_i * cost);
    p.minimise(cost);

    auto [propagators, verdicts] = analyse(p);
    REQUIRE(verdicts.size() == ds.size());
    for (const auto & d : ds) {
        auto v = verdict_on(verdicts, d);
        REQUIRE(v);
        CHECK_FALSE(v->needed);
    }

    // The index variables, on the other hand, have their interiors read: the
    // not-equals only by instantiation, but every element's own index
    // propagator reads the other index's whole domain. A probe pair on one of
    // them, belonging to no constraint in the model, sees that.
    propagators.install_with_optional_interior_pruning(NamedConstraint{"probe"}, {xs[0]}, does_nothing(), Triggers{}, does_nothing(), Triggers{});
    auto probe = verdict_on(propagators.analyse_optional_interior_pruning(), xs[0]);
    REQUIRE(probe);
    CHECK(probe->needed);
}

TEST_CASE("Auto propagates exactly as the arm it chose, counts and all")
{
    // A pair runs its live member exactly as that propagator would run
    // installed alone: the same wakes, and the same idempotence verdict, so
    // the same number of propagations, not merely the same tree. With nothing
    // else reading the results, solve_with() switches every element to BC;
    // with each result also equal to some other variable, it keeps them all
    // on GAC.
    vector<vector<Integer>> distances{{0_i, 3_i, 7_i, 2_i}, {3_i, 0_i, 5_i, 9_i}, {7_i, 5_i, 0_i, 4_i}, {2_i, 9_i, 4_i, 0_i}};
    auto run = [&](const ElementConsistency & level, bool observed) {
        Problem p;
        auto xs = p.create_integer_variable_vector(4, 0_i, 3_i, "xs");
        for (int i = 0; i < 4; ++i)
            for (int j = i + 1; j < 4; ++j)
                p.post(NotEquals{xs[i], xs[j]});
        WeightedSum wcosts;
        for (int i = 0; i < 4; ++i)
            for (int j = 0; j < 4; ++j) {
                auto d = p.create_integer_variable(0_i, 10_i);
                p.post(Element2DConstantArray{d, xs[i], xs[j], &distances}.with_consistency(level));
                if (observed)
                    p.post(Equals{d, p.create_integer_variable(0_i, 10_i)});
                wcosts += Integer{i + j + 1} * d;
            }
        auto cost = p.create_integer_variable(0_i, 100000_i, "cost");
        p.post(std::move(wcosts) == 1_i * cost);
        p.minimise(cost);
        auto stats = solve_with(
            p, SolveCallbacks{.branch = branch_with(variable_order::dom(xs), value_order::smallest_in()), .stats_report = silent_stats_report()});
        return std::tuple{stats.recursions, stats.propagations, stats.effectful_propagations, stats.solutions};
    };
    CHECK(run(consistency::Auto{}, false) == run(consistency::BC{}, false));
    CHECK(run(consistency::Auto{}, true) == run(consistency::GAC{}, true));
}

TEST_CASE("tsp: nothing can observe an element result's interior")
{
    // The shape of minicp_benchmarks/tsp: dist_i = D[i][succ_i], summed into
    // the objective, over a circuit.
    vector<vector<Integer>> distances{
        {0_i, 4_i, 8_i, 3_i, 6_i}, {4_i, 0_i, 2_i, 7_i, 5_i}, {8_i, 2_i, 0_i, 9_i, 1_i}, {3_i, 7_i, 9_i, 0_i, 6_i}, {6_i, 5_i, 1_i, 6_i, 0_i}};
    auto n = distances.size();

    Problem p;
    auto succ = p.create_integer_variable_vector(n, 0_i, Integer(n - 1));
    auto dist = p.create_integer_variable_vector(n, 0_i, 9_i);
    p.post(Circuit{succ});
    for (unsigned i = 0; i < n; ++i)
        p.post(ElementConstantArray{dist[i], succ[i], &distances[i]}.with_consistency(consistency::Auto{}));
    auto obj = p.create_integer_variable(0_i, 1000_i, "obj");
    WeightedSum dist_sum;
    for (auto & s : dist)
        dist_sum += 1_i * s;
    p.post(dist_sum == 1_i * obj);
    p.minimise(obj);

    auto [propagators, verdicts] = analyse(p);
    REQUIRE(verdicts.size() == n);
    for (const auto & v : verdicts)
        CHECK_FALSE(v.needed);

    propagators.install_with_optional_interior_pruning(NamedConstraint{"probe"}, {succ[0]}, does_nothing(), Triggers{}, does_nothing(), Triggers{});
    auto probe = verdict_on(propagators.analyse_optional_interior_pruning(), succ[0]);
    REQUIRE(probe);
    CHECK(probe->needed);
}

TEST_CASE("An element result's interior is observed only by constraints that can see holes")
{
    vector<Integer> array{1_i, 5_i, 9_i};

    SECTION("equality with another variable observes it")
    {
        Problem p;
        auto idx = p.create_integer_variable(0_i, 2_i);
        auto result = p.create_integer_variable(0_i, 10_i);
        auto other = p.create_integer_variable(0_i, 10_i);
        p.post(ElementConstantArray{result, idx, &array}.with_consistency(consistency::Auto{}));
        p.post(Equals{result, other});
        auto [propagators, verdicts] = analyse(p);
        auto v = verdict_on(verdicts, result);
        REQUIRE(v);
        CHECK(v->needed);
        REQUIRE(v->observed_by);
    }

    SECTION("an unconditional not-equals does not: it only ever asks whether its operands are fixed")
    {
        Problem p;
        auto idx = p.create_integer_variable(0_i, 2_i);
        auto result = p.create_integer_variable(0_i, 10_i);
        auto other = p.create_integer_variable(0_i, 10_i);
        p.post(ElementConstantArray{result, idx, &array}.with_consistency(consistency::Auto{}));
        p.post(NotEquals{result, other});
        auto [propagators, verdicts] = analyse(p);
        auto v = verdict_on(verdicts, result);
        REQUIRE(v);
        CHECK_FALSE(v->needed);
    }

    SECTION("an all-different does")
    {
        Problem p;
        auto idx = p.create_integer_variable(0_i, 2_i);
        auto result = p.create_integer_variable(0_i, 10_i);
        auto other = p.create_integer_variable(0_i, 10_i);
        p.post(ElementConstantArray{result, idx, &array}.with_consistency(consistency::Auto{}));
        p.post(AllDifferent{{result, other}});
        auto [propagators, verdicts] = analyse(p);
        auto v = verdict_on(verdicts, result);
        REQUIRE(v);
        CHECK(v->needed);
    }

    SECTION("a second element with the same result does, each observing the other")
    {
        Problem p;
        auto idx1 = p.create_integer_variable(0_i, 2_i);
        auto idx2 = p.create_integer_variable(0_i, 2_i);
        auto result = p.create_integer_variable(0_i, 10_i);
        p.post(ElementConstantArray{result, idx1, &array}.with_consistency(consistency::Auto{}));
        p.post(ElementConstantArray{result, idx2, &array}.with_consistency(consistency::Auto{}));
        auto [propagators, verdicts] = analyse(p);
        REQUIRE(verdicts.size() == 2);
        CHECK(verdicts.at(0).needed);
        CHECK(verdicts.at(1).needed);
    }

    SECTION("an element whose result is another element's array entry")
    {
        // e1 has a variable array containing y; e2 computes y. e1's index
        // propagator reads y's interior, so e2's pruning is needed. e1 itself
        // declares no pair at all, since its array has variable entries.
        Problem p;
        auto idx1 = p.create_integer_variable(0_i, 1_i);
        auto idx2 = p.create_integer_variable(0_i, 2_i);
        auto y = p.create_integer_variable(0_i, 10_i);
        auto w = p.create_integer_variable(0_i, 10_i);
        auto result = p.create_integer_variable(0_i, 10_i);
        vector<IntegerVariableID> entries{y, w};
        p.post(Element{result, idx1, &entries}.with_consistency(consistency::Auto{}));
        p.post(ElementConstantArray{y, idx2, &array}.with_consistency(consistency::Auto{}));
        auto [propagators, verdicts] = analyse(p);
        REQUIRE(verdicts.size() == 1);
        auto on_y = verdict_on(verdicts, y);
        REQUIRE(on_y);
        CHECK(on_y->needed);
    }
}

TEST_CASE("Which elements declare an optional pruning")
{
    vector<Integer> array{1_i, 5_i, 9_i};

    SECTION("explicit GAC and BC do not")
    {
        for (auto level : {ElementConsistency{consistency::GAC{}}, ElementConsistency{consistency::BC{}}}) {
            Problem p;
            auto idx = p.create_integer_variable(0_i, 2_i);
            auto result = p.create_integer_variable(0_i, 10_i);
            p.post(ElementConstantArray{result, idx, &array}.with_consistency(level));
            auto [propagators, verdicts] = analyse(p);
            CHECK(verdicts.empty());
        }
    }

    SECTION("variable entries keep GAC")
    {
        Problem p;
        auto idx = p.create_integer_variable(0_i, 2_i);
        auto result = p.create_integer_variable(0_i, 10_i);
        vector<IntegerVariableID> entries{p.create_integer_variable(0_i, 10_i), constant_variable(5_i), constant_variable(9_i)};
        p.post(Element{result, idx, &entries}.with_consistency(consistency::Auto{}));
        auto [propagators, verdicts] = analyse(p);
        CHECK(verdicts.empty());
    }

    SECTION("an array of variables that are all fixed pairs, like a constant one")
    {
        Problem p;
        auto idx = p.create_integer_variable(0_i, 2_i);
        auto result = p.create_integer_variable(0_i, 10_i);
        vector<IntegerVariableID> entries{constant_variable(1_i), constant_variable(5_i), constant_variable(9_i)};
        p.post(Element{result, idx, &entries}.with_consistency(consistency::Auto{}));
        auto [propagators, verdicts] = analyse(p);
        REQUIRE(verdicts.size() == 1);
        CHECK_FALSE(verdicts.at(0).needed);
    }

    SECTION("the result doubling as the index keeps GAC")
    {
        Problem p;
        auto idx = p.create_integer_variable(0_i, 2_i);
        vector<Integer> small{0_i, 2_i, 1_i};
        p.post(ElementConstantArray{idx, idx, &small}.with_consistency(consistency::Auto{}));
        auto [propagators, verdicts] = analyse(p);
        CHECK(verdicts.empty());
    }
}
