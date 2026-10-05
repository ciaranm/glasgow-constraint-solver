#include <gcs/constraints/regular/canonical_run.hh>
#include <gcs/innards/state.hh>

#include <catch2/catch_test_macros.hpp>

#include <set>
#include <unordered_map>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::pair;
using std::set;
using std::unordered_map;
using std::vector;

namespace
{
    using Transitions = vector<unordered_map<Integer, set<long>>>;

    auto ambiguous(const vector<pair<Integer, Integer>> & domains, const Transitions & transitions, const vector<long> & final_states) -> bool
    {
        State state;
        vector<IntegerVariableID> vars;
        for (const auto & [lower, upper] : domains)
            vars.emplace_back(state.allocate_integer_variable_with_state(lower, upper));
        return regular_is_ambiguous(vars, transitions, final_states, state);
    }
}

TEST_CASE("A deterministic automaton is not ambiguous")
{
    // Even number of 0s.
    CHECK(! ambiguous({{0_i, 1_i}, {0_i, 1_i}, {0_i, 1_i}}, {{{0_i, {1}}, {1_i, {0}}}, {{0_i, {0}}, {1_i, {1}}}}, {0}));
}

TEST_CASE("Two accepting runs on one symbol")
{
    // The automaton for "0|0": reading 0 goes to either of two final states.
    Transitions zero_or_zero{{{0_i, {1, 2}}}, {}, {}};
    CHECK(ambiguous({{0_i, 1_i}}, zero_or_zero, {1, 2}));
    // With only one of the targets final, each word has one accepting run.
    CHECK(! ambiguous({{0_i, 1_i}}, zero_or_zero, {1}));
}

TEST_CASE("Runs that split and then fail are not ambiguous")
{
    // After 0 the runs split; only one of them can read each second symbol.
    CHECK(! ambiguous({{0_i, 1_i}, {0_i, 1_i}}, {{{0_i, {1, 2}}}, {{1_i, {3}}}, {{0_i, {3}}}, {}}, {3}));
}

TEST_CASE("Runs that split and meet again are ambiguous")
{
    CHECK(ambiguous({{0_i, 1_i}, {0_i, 1_i}}, {{{0_i, {1, 2}}}, {{1_i, {3}}}, {{1_i, {3}}}, {}}, {3}));
}

TEST_CASE("Ambiguity depends on the domains")
{
    // Only the value 2 splits the run.
    Transitions split_on_two{{{0_i, {1}}, {2_i, {1, 2}}}, {}, {}};
    CHECK(! ambiguous({{0_i, 1_i}}, split_on_two, {1, 2}));
    CHECK(ambiguous({{0_i, 2_i}}, split_on_two, {1, 2}));
    CHECK(! ambiguous({{0_i, 0_i}}, split_on_two, {1, 2}));
}

TEST_CASE("Ambiguity depends on the length")
{
    // "Contains a 1", guessing which 1: a word has one accepting run per 1 in
    // it, so the single-symbol words have at most one.
    Transitions contains_a_one{{{0_i, {0}}, {1_i, {0, 1}}}, {{0_i, {1}}, {1_i, {1}}}};
    CHECK(! ambiguous({{0_i, 1_i}}, contains_a_one, {1}));
    CHECK(ambiguous({{0_i, 1_i}, {0_i, 1_i}}, contains_a_one, {1}));
    // With the first symbol fixed to 0, two symbols are not enough either.
    CHECK(! ambiguous({{0_i, 0_i}, {0_i, 1_i}}, contains_a_one, {1}));
}

TEST_CASE("No accepting word, no ambiguity")
{
    CHECK(! ambiguous({{0_i, 1_i}}, {{{0_i, {1, 2}}}, {}, {}}, {}));
    CHECK(! ambiguous({}, {{{0_i, {1, 2}}}, {}, {}}, {0}));
}
