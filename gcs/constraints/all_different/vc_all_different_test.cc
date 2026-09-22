/* The prebuilt single-value reasons shared by the VC propagator and the first
 * stage of staged GAC (issue #1008).
 *
 * A lookup that misses is invisible to every solver-level test: the propagator
 * falls back to building an equivalent reason inline, so solutions, search trees
 * and proofs all come out the same. And the property the issue is about, that the
 * storage follows the scope rather than the span of its variable IDs, is a memory
 * cost no correctness test sees either. So both are checked here directly, on a
 * scope whose IDs are deliberately far apart. */

#include <gcs/constraints/all_different/vc_all_different.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>
#include <gcs/problem.hh>

#include <catch2/catch_test_macros.hpp>

#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::vector;

TEST_CASE("Single-value reasons are sized by the scope, not the span of its IDs")
{
    Problem p;
    auto a = p.create_integer_variable(3_i, 3_i);
    auto gap = p.create_integer_variable_vector(10000, 0_i, 5_i);
    auto b = p.create_integer_variable(4_i, 4_i);
    auto more_gap = p.create_integer_variable_vector(10000, 0_i, 5_i);
    auto c = p.create_integer_variable(5_i, 5_i);
    auto outside = gap.at(5000);

    // Out of ID order, with a view and a constant that must get no entry.
    auto view = a + 10_i;
    auto constant = constant_variable(7_i);
    vector<IntegerVariableID> scope{c, view, a, constant, b};

    auto reasons = NonGacAllDifferentSingleValueReasons::build(scope);
    CHECK(reasons.indices.size() == 3);
    CHECK(reasons.reasons.size() == 3);

    auto state = p.create_state_for_new_search(nullptr);
    for (const auto & [var, val] : vector<std::pair<IntegerVariableID, Integer>>{{a, 3_i}, {b, 4_i}, {c, 5_i}}) {
        auto found = reasons.find(var);
        REQUIRE(found);
        auto literals = materialise(*found, state);
        REQUIRE(literals.size() == 1);
        CHECK(literals.front() == ProofLiteralOrFlag{var == val});
    }

    CHECK(! reasons.find(view));
    CHECK(! reasons.find(constant));
    CHECK(! reasons.find(outside));
    CHECK(! reasons.find(more_gap.back()));
}
