#include <gcs/constraints/extensional_utils.hh>
#include <gcs/constraints/table.hh>
#include <gcs/current_state.hh>
#include <gcs/extensional.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>
#include <gcs/stats.hh>

#include <catch2/catch_test_macros.hpp>

#include <memory>
#include <set>
#include <tuple>
#include <utility>

using namespace gcs;

using std::make_shared;

// Issue #7: Table and NegativeTable take their tuples as an ArrayParam, so a
// caller can hand over a shared_ptr and have the data shared rather than copied
// -- and clone() shares the same buffer too rather than duplicating it. Nothing
// in the tree exercises the shared path, so pin it down here via use_count(): a
// deep copy would leave the original buffer at a use count of one.
TEST_CASE("Table shares tuple storage rather than copying it")
{
    Problem problem;
    auto x = problem.create_integer_variable(0_i, 3_i);
    auto y = problem.create_integer_variable(0_i, 3_i);

    auto tuples = make_shared<const SimpleTuples>(SimpleTuples{{0_i, 1_i}, {2_i, 3_i}});
    REQUIRE(tuples.use_count() == 1);

    Table table{{x, y}, ExtensionalTuples{ArrayParam<SimpleTuples>{tuples}}};
    // The table holds the same buffer, not a deep copy.
    CHECK(tuples.use_count() == 2);

    auto cloned = table.clone();
    // clone() shares the buffer rather than duplicating it.
    CHECK(tuples.use_count() == 3);
}

TEST_CASE("NegativeTable shares tuple storage rather than copying it")
{
    Problem problem;
    auto x = problem.create_integer_variable(0_i, 3_i);
    auto y = problem.create_integer_variable(0_i, 3_i);

    auto tuples = make_shared<const SimpleTuples>(SimpleTuples{{0_i, 1_i}, {2_i, 3_i}});
    REQUIRE(tuples.use_count() == 1);

    NegativeTable table{{x, y}, ExtensionalTuples{ArrayParam<SimpleTuples>{tuples}}};
    CHECK(tuples.use_count() == 2);

    auto cloned = table.clone();
    CHECK(tuples.use_count() == 3);
}

// Issue #508: sharing the tuples means sharing what a propagator derives from
// them. The compact table's support masks are the biggest thing it holds and a
// pure function of the tuples, so every Table over one tupleset uses one copy:
// a crossword posts twenty tables over one dictionary, and twenty copies of the
// same 146 KB does not fit in cache where one copy does.

namespace
{
    // Two positions, values 0..7, a tuple wherever the two values differ. Big
    // enough to be a table worth a mask (see ExtensionalCompactTable::min_tuples)
    // and small enough to enumerate by hand below.
    auto not_equals_tuples() -> std::shared_ptr<const SimpleTuples>
    {
        SimpleTuples tuples;
        for (Integer a = 0_i; a < 8_i; ++a)
            for (Integer b = 0_i; b < 8_i; ++b)
                if (a != b)
                    tuples.push_back({a, b});
        return make_shared<const SimpleTuples>(std::move(tuples));
    }
}

TEST_CASE("Tables over one tupleset share one set of support masks")
{
    Problem problem;
    auto x = problem.create_integer_variable(0_i, 7_i);
    auto y = problem.create_integer_variable(0_i, 7_i);
    auto z = problem.create_integer_variable(0_i, 7_i);

    auto tuples = not_equals_tuples();
    for (auto [a, b] : {std::pair{x, y}, std::pair{y, z}, std::pair{x, z}})
        problem.post(Table{{a, b}, ExtensionalTuples{ArrayParam<SimpleTuples>{tuples}}}.with_algorithm(table::CompactTable{}));

    Stats stats;
    auto state = problem.create_state_for_new_search(nullptr);
    auto propagators = problem.create_propagators(state, stats, nullptr);

    // Same pin as the tuple-storage tests above: asking the store for the masks
    // hands back what the three constraints are holding, so a use count above
    // two says they found each other's rather than each making its own. (One
    // for the store, one for the local here, one per constraint.)
    auto masks = propagators.shared_derived_data<innards::ExtensionalSupportMasks>(&*tuples);
    CHECK(masks.use_count() == 5);
}

TEST_CASE("Tables sharing support masks solve the same as tables that do not")
{
    auto tuples = not_equals_tuples();

    auto enumerate = [&](bool share) {
        Problem problem;
        auto x = problem.create_integer_variable(0_i, 7_i);
        auto y = problem.create_integer_variable(0_i, 7_i);
        auto z = problem.create_integer_variable(0_i, 7_i);

        // Unshared posts a copy of the same tuples per constraint, which is the
        // same constraint over the same values and so must have the same
        // solutions -- only the first constraint to want masks builds any.
        for (auto [a, b] : {std::pair{x, y}, std::pair{y, z}, std::pair{x, z}})
            problem.post(Table{{a, b},
                share ? ExtensionalTuples{ArrayParam<SimpleTuples>{tuples}} : ExtensionalTuples{ArrayParam<SimpleTuples>{SimpleTuples{*tuples}}}}
                    .with_algorithm(table::CompactTable{}));

        std::set<std::tuple<long long, long long, long long>> solutions;
        solve_with(problem, SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
            solutions.emplace(s(x).raw_value, s(y).raw_value, s(z).raw_value);
            return true;
        }});
        return solutions;
    };

    auto shared = enumerate(true);
    // 8 * 7 * 6 all-different triples over 0..7.
    CHECK(shared.size() == 336);
    CHECK(shared == enumerate(false));
}
