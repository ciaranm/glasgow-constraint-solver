#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <catch2/catch_test_macros.hpp>

#include <cstdlib>
#include <iostream>
#include <map>
#include <memory>
#include <sstream>
#include <string>

using namespace gcs;
using namespace gcs::innards;

// The per-constraint-type propagator report: GCS_PROPAGATOR_STATS. What is
// asserted here is the arithmetic and the grouping, on propagators whose
// behaviour is written out in front of the figures, because a counter wired to
// the wrong branch reports a plausible number for ever.

namespace
{
    // GCS_PROPAGATOR_STATS is read once per Propagators construction rather than
    // into a static, so a test can set it around the object it wants it to
    // affect. Restore on the way out: the test binary shares one environment.
    // MSVC has no POSIX setenv / unsetenv, and on Windows _putenv_s(name, "")
    // removes the variable.
    struct WithPropagatorStats final
    {
        explicit WithPropagatorStats(const char * const value)
        {
#if defined(_WIN32)
            _putenv_s("GCS_PROPAGATOR_STATS", value);
#else
            setenv("GCS_PROPAGATOR_STATS", value, 1);
#endif
        }

        ~WithPropagatorStats()
        {
#if defined(_WIN32)
            _putenv_s("GCS_PROPAGATOR_STATS", "");
#else
            unsetenv("GCS_PROPAGATOR_STATS");
#endif
        }

        WithPropagatorStats(const WithPropagatorStats &) = delete;
        auto operator=(const WithPropagatorStats &) -> WithPropagatorStats & = delete;
    };

    [[nodiscard]] auto component_named(const Stats & stats, const std::string & name) -> std::shared_ptr<const ComponentStats>
    {
        for (const auto & component : stats.components())
            if (component->component_name() == name)
                return component;
        return nullptr;
    }

    [[nodiscard]] auto propagator_call_entries(const Stats & stats) -> std::map<std::string, long long>
    {
        std::map<std::string, long long> result;
        const auto block = component_named(stats, "propagator_calls");
        REQUIRE(block);
        for (const auto & entry : block->entries())
            result.emplace(entry.name, entry.value);
        return result;
    }

    // Caps x at 5 in one go, and is not idempotent-claiming, so the engine wakes
    // it a second time with its own inference: one effectful run then one no-op.
    auto install_capping_propagator(Propagators & propagators, SimpleIntegerVariableID x) -> void
    {
        Triggers triggers;
        triggers.on_change = {x};
        propagators.install(
            ConstraintID{NumberedConstraint{1}},
            [x](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                if (state.upper_bound(x) > 5_i)
                    inference.infer(logger, x < 6_i, NoJustificationNeeded{}, NoReason{});
                return PropagatorState::Enable;
            },
            triggers);
    }

    // Watches y, which nothing here ever changes, so it runs exactly once: the
    // start-of-search call every propagator gets.
    auto install_idle_propagator(Propagators & propagators, SimpleIntegerVariableID y) -> void
    {
        Triggers triggers;
        triggers.on_change = {y};
        propagators.install(
            ConstraintID{NumberedConstraint{2}},
            [](const State &, auto &, ProofLogger * const) -> PropagatorState { return PropagatorState::Enable; }, triggers);
    }
}

TEST_CASE("No block is registered when GCS_PROPAGATOR_STATS is unset")
{
    State state;
    Stats stats;
    Propagators propagators{stats};
    auto x = state.allocate_integer_variable_with_state(0_i, 10_i);
    install_capping_propagator(propagators, x);

    REQUIRE(propagators.propagate(Literals{}, state, nullptr));
    propagators.fill_in_constraint_stats(stats);

    // An unasked-for component has not done nothing, it has not run: a line on
    // every solve naming an environment variable would be noise.
    CHECK(! component_named(stats, "propagator_calls"));
    // The aggregate counters are unaffected either way.
    CHECK(stats.propagations == 2);
    CHECK(stats.effectful_propagations == 1);
}

TEST_CASE("Calls, effectful runs and contradictions are counted per constraint type")
{
    WithPropagatorStats asked{"calls"};

    State state;
    Stats stats;
    Propagators propagators{stats};
    auto x = state.allocate_integer_variable_with_state(0_i, 10_i);
    auto y = state.allocate_integer_variable_with_state(0_i, 10_i);

    install_capping_propagator(propagators, x);
    propagators.note_propagator_types(0, "capper");
    install_idle_propagator(propagators, y);
    propagators.note_propagator_types(1, "idler");

    REQUIRE(propagators.propagate(Literals{}, state, nullptr));
    REQUIRE(state.upper_bound(x) == 5_i);
    propagators.fill_in_constraint_stats(stats);

    const auto entries = propagator_call_entries(stats);
    // The capper is woken by its own inference, so it runs twice: once
    // effectfully and once as the no-op that establishes the fixpoint.
    CHECK(entries.at("capper_constraints") == 1);
    CHECK(entries.at("capper_propagators") == 1);
    CHECK(entries.at("capper_calls") == 2);
    CHECK(entries.at("capper_effectful") == 1);
    CHECK(entries.at("capper_contradictions") == 0);
    // The idler gets the start-of-search call and nothing else.
    CHECK(entries.at("idler_calls") == 1);
    CHECK(entries.at("idler_effectful") == 0);
    // The counts add up to the aggregates, which is the property that catches a
    // counter wired to the wrong branch.
    CHECK(entries.at("capper_calls") + entries.at("idler_calls") == static_cast<long long>(stats.propagations));
    CHECK(entries.at("capper_effectful") + entries.at("idler_effectful") == static_cast<long long>(stats.effectful_propagations));
    // The calls rung reads no clock, so there is no time column to read.
    CHECK(! entries.contains("capper_micros"));
}

TEST_CASE("A contradicting propagator is counted under its own type")
{
    WithPropagatorStats asked{"calls"};

    State state;
    Stats stats;
    Propagators propagators{stats};
    auto x = state.allocate_integer_variable_with_state(0_i, 10_i);

    Triggers triggers;
    triggers.on_change = {x};
    propagators.install(
        ConstraintID{NumberedConstraint{1}},
        [](const State &, auto & inference, ProofLogger * const logger) -> PropagatorState {
            inference.contradiction(logger, JustifyUsingRUP{}, NoReason{});
            return PropagatorState::Enable;
        },
        triggers);
    propagators.note_propagator_types(0, "failer");

    REQUIRE(! propagators.propagate(Literals{}, state, nullptr));
    propagators.fill_in_constraint_stats(stats);

    const auto entries = propagator_call_entries(stats);
    CHECK(entries.at("failer_calls") == 1);
    CHECK(entries.at("failer_contradictions") == 1);
    CHECK(entries.at("failer_effectful") == 0);
    CHECK(entries.at("failer_contradictions") == static_cast<long long>(stats.contradicting_propagations));
}

TEST_CASE("An already-labelled propagator keeps its own type")
{
    WithPropagatorStats asked{"calls"};

    State state;
    Stats stats;
    Propagators propagators{stats};
    auto x = state.allocate_integer_variable_with_state(0_i, 10_i);
    auto y = state.allocate_integer_variable_with_state(0_i, 10_i);

    // The shape a child constraint makes: the child's install() labels its own
    // propagator, and the parent's call then covers a range that includes it.
    install_capping_propagator(propagators, x);
    propagators.note_propagator_types(0, "child");
    install_idle_propagator(propagators, y);
    propagators.note_propagator_types(0, "parent");

    REQUIRE(propagators.propagate(Literals{}, state, nullptr));
    propagators.fill_in_constraint_stats(stats);

    const auto entries = propagator_call_entries(stats);
    CHECK(entries.at("child_calls") == 2);
    CHECK(entries.at("parent_calls") == 1);
    // The parent did not swallow the child, which is the whole point of doing
    // the labelling in Constraint::install() rather than at each install site.
    CHECK(! entries.contains("child_parent_calls"));
}

TEST_CASE("A propagator no constraint claimed is reported as unlabelled")
{
    WithPropagatorStats asked{"calls"};

    State state;
    Stats stats;
    Propagators propagators{stats};
    auto x = state.allocate_integer_variable_with_state(0_i, 10_i);
    install_capping_propagator(propagators, x);

    REQUIRE(propagators.propagate(Literals{}, state, nullptr));
    propagators.fill_in_constraint_stats(stats);

    // Nothing routed this one through Constraint::install(), which is how the
    // learned-nogoods store's propagator arrives. It is still counted.
    const auto entries = propagator_call_entries(stats);
    CHECK(entries.at("unlabelled_calls") == 2);
}

TEST_CASE("The time rung adds a per-type time the calls rung does not")
{
    WithPropagatorStats asked{"time"};

    State state;
    Stats stats;
    Propagators propagators{stats};
    auto x = state.allocate_integer_variable_with_state(0_i, 10_i);
    install_capping_propagator(propagators, x);
    propagators.note_propagator_types(0, "capper");

    REQUIRE(propagators.propagate(Literals{}, state, nullptr));
    propagators.fill_in_constraint_stats(stats);

    // The elapsed time of two trivial runs rounds to zero microseconds on any
    // machine worth running this on, so what is asserted is that the column is
    // there at all, and that asking for time did not lose the counts.
    const auto entries = propagator_call_entries(stats);
    CHECK(entries.contains("capper_micros"));
    CHECK(entries.at("capper_micros") >= 0);
    CHECK(entries.at("capper_calls") == 2);
}

TEST_CASE("An unrecognised GCS_PROPAGATOR_STATS value is ignored with a warning")
{
    WithPropagatorStats asked{"yes please"};

    std::ostringstream captured;
    auto old = std::cerr.rdbuf(captured.rdbuf());
    State state;
    Stats stats;
    Propagators propagators{stats};
    std::cerr.rdbuf(old);

    auto x = state.allocate_integer_variable_with_state(0_i, 10_i);
    install_capping_propagator(propagators, x);
    REQUIRE(propagators.propagate(Literals{}, state, nullptr));
    propagators.fill_in_constraint_stats(stats);

    CHECK(captured.str().find("GCS_PROPAGATOR_STATS") != std::string::npos);
    CHECK(! component_named(stats, "propagator_calls"));
}
