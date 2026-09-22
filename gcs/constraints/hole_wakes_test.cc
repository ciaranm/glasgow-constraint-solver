/* Holes that some other propagator punches must wake the propagators they
 * affect (issue #966).
 *
 * Count, SubCircuit (under Prevent) and BinPacking (under the upfront Stage 3
 * strategy) each ask whether a value that is usually interior is still in a
 * variable's domain, and each used to watch that variable only for its bounds
 * or its instantiation. Nothing woke them when the hole appeared, so they drew
 * the inference only if something else happened to wake them later. That never
 * fails a test on its own: the solver stays sound, and the constraint tests
 * post one constraint at a time, so only that constraint punches holes and
 * every branching decision wakes everything on its variable anyway.
 *
 * So each case here punches the hole from a separate propagator that is woken
 * by nothing but an unrelated variable `t`, then checks that the constraint
 * drew the inference the hole licenses. Each passes only if the hole itself
 * woke the constraint. */

#include <gcs/constraints/bin_packing.hh>
#include <gcs/constraints/circuit.hh>
#include <gcs/constraints/count.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>
#include <gcs/stats.hh>

#include <catch2/catch_test_macros.hpp>

#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::vector;

namespace
{
    // Once t is fixed to 1, remove each of `holes` from `victim`. Woken by t alone.
    auto install_hole_puncher(Propagators & propagators, SimpleIntegerVariableID t, IntegerVariableID victim, vector<Integer> holes) -> void
    {
        Triggers triggers;
        triggers.on_change = {t};
        propagators.install(
            ConstraintID{NumberedConstraint{999}},
            [t, victim, holes](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                if (state.optional_single_value(t) == 1_i)
                    for (const auto & h : holes)
                        inference.infer(logger, victim != h, NoJustificationNeeded{}, NoReason{});
                return PropagatorState::Enable;
            },
            triggers);
    }

    // Branch t = 1 as search would. The guess wakes only what watches t, which is the
    // hole puncher.
    auto branch_t_is_one(State & state, Propagators & propagators, SimpleIntegerVariableID t) -> bool
    {
        state.guess(t == 1_i);
        return propagators.propagate(Literals{t == 1_i}, state, nullptr);
    }
}

TEST_CASE("A hole in how_many wakes Count")
{
    State state;
    Stats stats;
    Propagators propagators{stats};

    // x1 is 2 and x2, x3 can never be 2, so a value of interest of 2 can only ever
    // be counted once. Once 1 leaves how_many that count is gone, and so is voi = 2.
    auto x1 = state.allocate_integer_variable_with_state(2_i, 2_i);
    auto x2 = state.allocate_integer_variable_with_state(1_i, 3_i);
    auto x3 = state.allocate_integer_variable_with_state(1_i, 3_i);
    REQUIRE(state.infer(x2 != 2_i) == Inference::InteriorValuesChanged);
    REQUIRE(state.infer(x3 != 2_i) == Inference::InteriorValuesChanged);
    auto voi = state.allocate_integer_variable_with_state(1_i, 2_i);
    auto how_many = state.allocate_integer_variable_with_state(0_i, 2_i);
    auto t = state.allocate_integer_variable_with_state(0_i, 1_i);

    Count{{x1, x2, x3}, voi, how_many}.install(propagators, state, nullptr);
    install_hole_puncher(propagators, t, how_many, {1_i});

    REQUIRE(propagators.propagate(Literals{}, state, nullptr));
    REQUIRE(state.in_domain(voi, 2_i));

    (void)state.new_epoch();
    REQUIRE(branch_t_is_one(state, propagators, t));
    CHECK(! state.in_domain(how_many, 1_i));
    CHECK(state.optional_single_value(voi) == 1_i);
}

namespace
{
    // Four nodes, with node 0 fixed to point at node 1 and nodes 1 to 3 free to go to
    // 0, 2 or 3. The chain 0 -> 1 may still close through succ[1] = 0, which is
    // allowed while every other node may yet be a self loop. Once 2 leaves succ[2],
    // node 2 has to be on the tour, and so the chain must not close. `offset` builds
    // the successors as views over variables numbered from `offset`, which is how the
    // MiniZinc front end posts them.
    auto check_subcircuit_evidence_wake(Integer offset) -> void
    {
        State state;
        Stats stats;
        Propagators propagators{stats};

        vector<IntegerVariableID> succ;
        succ.push_back(state.allocate_integer_variable_with_state(1_i + offset, 1_i + offset) + -offset);
        for (int i = 1; i < 4; ++i) {
            auto s = state.allocate_integer_variable_with_state(offset, 3_i + offset);
            REQUIRE(state.infer(s != 1_i + offset) == Inference::InteriorValuesChanged);
            succ.push_back(s + -offset);
        }
        auto t = state.allocate_integer_variable_with_state(0_i, 1_i);

        SubCircuit{succ}.install(propagators, state, nullptr);
        install_hole_puncher(propagators, t, succ[2], {2_i});

        REQUIRE(propagators.propagate(Literals{}, state, nullptr));
        REQUIRE(state.in_domain(succ[1], 0_i));

        // Twice, backtracking in between: the watch that wakes SubCircuit is consumed
        // when it fires, and has to be back for the second branch.
        for (int round = 0; round < 2; ++round) {
            auto timestamp = state.new_epoch();
            REQUIRE(branch_t_is_one(state, propagators, t));
            CHECK(! state.in_domain(succ[2], 2_i));
            CHECK(! state.in_domain(succ[1], 0_i));
            state.backtrack(timestamp);
            REQUIRE(state.in_domain(succ[1], 0_i));
        }
    }
}

TEST_CASE("A node leaving its own index wakes the SubCircuit lookahead")
{
    check_subcircuit_evidence_wake(0_i);
}

TEST_CASE("A node leaving its own index wakes the SubCircuit lookahead through a view")
{
    check_subcircuit_evidence_wake(1_i);
}

TEST_CASE("A hole in a load wakes BinPacking's upfront Stage 3")
{
    State state;
    Stats stats;
    Propagators propagators{stats};

    // Sizes 1, 2 and 4 over two bins. Every load from 0 to 6 is reachable in bin 0,
    // but once 1, 3 and 5 leave it, every sum including item 0 (1, 3, 5, 7) is gone
    // from bin 0: 7 is past its upper bound and the rest are holes.
    vector<IntegerVariableID> items;
    for (int i = 0; i < 3; ++i)
        items.push_back(state.allocate_integer_variable_with_state(0_i, 1_i));
    auto load0 = state.allocate_integer_variable_with_state(0_i, 6_i);
    auto load1 = state.allocate_integer_variable_with_state(0_i, 7_i);
    auto t = state.allocate_integer_variable_with_state(0_i, 1_i);

    BinPacking bin_packing{items, {1_i, 2_i, 4_i}, vector<IntegerVariableID>{load0, load1}};
    bin_packing.with_proof_strategy(proof_strategy::Upfront{});
    std::move(bin_packing).install(propagators, state, nullptr);
    install_hole_puncher(propagators, t, load0, {1_i, 3_i, 5_i});

    REQUIRE(propagators.propagate(Literals{}, state, nullptr));
    REQUIRE(state.in_domain(items[0], 0_i));

    (void)state.new_epoch();
    REQUIRE(branch_t_is_one(state, propagators, t));
    CHECK(state.lower_bound(load0) == 0_i);
    CHECK(state.upper_bound(load0) == 6_i);
    CHECK(state.optional_single_value(items[0]) == 1_i);
}
